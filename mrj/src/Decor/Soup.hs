{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Decor.Soup where

import Control.Applicative
import Control.Monad hiding (fail)
import Control.Monad.Except
import Control.Monad.Fail as MonadFail
import Control.Monad.RWS
import Control.Monad.Writer

import Control.Comonad.Cofree

import Data.Either
import Data.Either.Combinators
import Data.List (elemIndex)
import Data.Maybe
import Data.Typeable
import Text.Read (readMaybe)

import Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap

import Lens.Micro.Platform

import Generics.OneLiner
import Generics.OneLiner.Internal (FunConstraints, Result)
import GHC.Generics (Generic)
import GHC.TypeLits

import qualified Decor.Parser as P
import Decor.Types
import Decor.Types.Convert

-- | Constraints.
data K where
  KEqDC :: DCId -> RHS -> K
  -- ^ @t = u[sub]@. Term equality.

  KType :: Ctx -> DCId -> DCId -> K
  -- ^ @G |- t : u@. Typing judgement.

  KTypeC :: Ctx -> Ctx' -> CoercionId -> EqProp DCId -> K
  -- ^ @G |- g : a ~ b@. Coercion typing judgement.

  KRel :: Rel -> DCId -> K
  -- ^ @r & x <- |t|@. Relevance check.

  KWF :: Ctx -> K
  -- ^ @|- G@. Well-formed context.

  KOK :: Ctx -> EqProp DCId -> K
  -- ^ @G |- phi OK@. Well-formed equality proposition.

  K_ :: K -> K
  -- ^ Redundant constraints.

  deriving (Eq, Show)

data Params = Params
  { _showEqualities :: Bool
  , _relevance :: Bool
  , _boring :: Bool
  , _absurd :: Bool
  , _pruning :: Int
  , _jumping :: Int
  , _iniTerm :: DCoreP
  , _iniType :: DCoreP
  , _noConstants :: Bool
  , _guessSub :: Bool
  , _coercions :: Bool
  } deriving Generic

newtype PartialToSoup m a = PartialToSoup
  { unPartialToSoup :: RWST [String] [K] () m a }
  deriving (Functor, Applicative, Monad, MonadFail)

partialToSoup :: Functor m => ([String] -> m (a, [K])) -> PartialToSoup m a
partialToSoup f = PartialToSoup . RWST $ \r () ->
  fmap (\(a, ks) -> (a, (), ks)) (f r)

runPartialToSoup :: Functor m => PartialToSoup m a -> [String] -> m (a, [K])
runPartialToSoup m ctx =
  fmap (\(a, (), ks) -> (a, ks)) (runRWST (unPartialToSoup m) ctx ())

instance MonadSoup m => Converter Partial Soup (PartialToSoup m) where
  convertVar v = partialToSoup $ \ctx ->
    case elemIndex v ctx of
      Nothing -> MonadFail.fail $ "Unbound variable: " ++ show v
      Just i -> return (DeBruijnV (fromIntegral i), [])
  convertFun f =
    case readMaybe f of
      Nothing -> MonadFail.fail $ "Unknown constant: " ++ show f
      Just f -> return f
  bindV v k = k () $ \m -> partialToSoup $ \ctx -> runPartialToSoup m (v : ctx)
  convert_ t = partialToSoup $ \ctx -> do
    u <- fresh
    ks <- ini' ctx u t
    return (u, ks)

ini :: MonadSoup m => DCId -> DCoreP -> m [K]
ini = ini' []

ini' :: [String] -> MonadSoup m => DCId -> DCoreP -> m [K]
ini' _ _ Nothing = return []
ini' ctx u (Just t) = do
  (t, ks) <- runPartialToSoup (convertDCore t) ctx
  return (KEqDC u (RHSHead t) : ks)

type WithParams = (?params :: Params)

showEqualities :: WithParams => Bool
showEqualities = _showEqualities ?params

relevance :: WithParams => Bool
relevance = _relevance ?params

boring :: WithParams => Bool
boring = _boring ?params

absurd :: WithParams => Bool
absurd = _absurd ?params

pruning :: WithParams => Int
pruning = _pruning ?params

jumping :: WithParams => Int
jumping = _jumping ?params

noConstants :: WithParams => Bool
noConstants = _noConstants ?params

guessSub :: WithParams => Bool
guessSub = _guessSub ?params

coercions :: WithParams => Bool
coercions = _coercions ?params

kEqDC :: DCId -> RHS -> K
kEqDC = KEqDC

data Sub = Sub
  { vSub :: Bimap VarId VarId
  , cSub :: Bimap CVarId CVarId
  } deriving (Eq, Show)

emptySub :: Sub
emptySub = Sub Bimap.empty Bimap.empty

isEmptySub :: Sub -> Bool
isEmptySub = (== emptySub)

subV :: VarId -> Sub -> Maybe VarId
subV v = Bimap.lookup v . vSub

insertSub :: VarId -> VarId -> Sub -> Sub
insertSub v1 v2 sub = sub { vSub = Bimap.insert v1 v2 (vSub sub) }

invSub :: Sub -> Sub
invSub (Sub vs cs) = Sub (Bimap.twist vs) (Bimap.twist cs)

composeBimap :: (Ord b, Ord c) => Bimap a b -> Bimap b c -> Bimap a c
composeBimap ma mb = Bimap.mapR (mb Bimap.!) ma

composeSub :: Sub -> Sub -> Sub
composeSub (Sub vs cs) (Sub vs' cs') =
  Sub (composeBimap vs vs') (composeBimap cs cs')

data RHS
  = RHSId DCId Shift
  | RHSHead (DCore_ Soup)
  | RHSSub DCId DCId
  | RHSSubC CoercionId DCId
  deriving (Eq, Ord, Show)

class (Monad m, MonadFresh m, MonadFail m) => MonadSoup m where
  pick :: (Show x, Typeable x) => String -> [(x, a)] -> m a

pick' :: (Show x, Typeable x, MonadSoup m) => String -> [x] -> m x
pick' d xs = pick d [(x, x) | x <- xs]

class Applicative m => MonadFresh m where
  freshI :: m Integer

class Fresh a where
  fresh :: MonadFresh m => m a

instance Fresh VarId where
  fresh = VarId <$> freshI

instance Fresh CVarId where
  fresh = CVarId <$> freshI

instance Fresh DCId where
  fresh = DCId <$> freshI

instance Fresh CoercionId where
  fresh = CoercionId <$> freshI

instance Fresh a => Fresh (EqProp a) where
  fresh = (:~:) <$> fresh <*> fresh

instance Fresh () where
  fresh = pure ()

freshes
  :: forall t m
  .  (Generic t, ADTRecord t, Constraints t Fresh, MonadFresh m)
  => m t
freshes = createA' (For :: For Fresh) fresh

data Ctx = Ctx
  { varCtx :: [Either (EqProp DCId) DCId]
  } deriving (Eq, Ord, Show)

t0 : ty0 : nat0 : etc1 = DCId <$> [-1, -2 ..] :: [DCId]
foldNatTy0 : etc2 = etc1

emptyCtx :: Ctx
emptyCtx = Ctx []

k0 :: [K]
k0 =
  -- Initial constraint
  --  |- t0 : ty0
  [ KType emptyCtx t0 ty0
  ]

natToNatTyDC
    :: DCore_ Soup
natToNatTyDC = Pi Rel () nat0 nat0

constants :: [(DCId, DCoreP)]
constants =
  [ (nat0, Just (Fun "Nat"))

  -- forall (r : *). Nat -> r -> (r -> r) -> r
  , (foldNatTy0, (\(Right r) -> r) (P.parseDC
      "forall r : * -> forall z : r -> forall s : (forall m : r -> r) -> forall n : Nat -> r"))
  ]

data Ctx' = Ctx' [DeBruijnV]
  deriving (Eq, Ord, Show)

cctx :: Ctx -> Ctx'
cctx ctx = Ctx' [toEnum i | (i, Left _) <- zip [0 ..] (varCtx ctx)]

pickVar :: MonadSoup m => Ctx -> m DeBruijnV
pickVar ctx = pick' "Var" [toEnum i | (i, Right _) <- zip [0 ..] (varCtx ctx)]

lookupVar :: DeBruijnV -> Ctx -> Maybe DCId
lookupVar (DeBruijnV n) ctx = (rightToMaybe <=< listToMaybe) $ drop (fromIntegral n) (varCtx ctx)

insertVar :: DCId -> Ctx -> Ctx
insertVar ty ctx = ctx { varCtx = Right ty : varCtx ctx }

pickCVar :: MonadSoup m => Ctx -> m DeBruijnV
pickCVar ctx = pick' "Var" [toEnum i | (i, Left _) <- zip [0 ..] (varCtx ctx)]

lookupCVar :: DeBruijnV -> Ctx -> Maybe (EqProp DCId)
lookupCVar (DeBruijnV n) ctx = (leftToMaybe <=< listToMaybe) $ drop (fromIntegral n) (varCtx ctx)

insertCVar :: EqProp DCId -> Ctx -> Ctx
insertCVar phi ctx = ctx { varCtx = Left phi : varCtx ctx }

typeCheck :: (WithParams, MonadSoup m) => Ctx -> DCId -> DCId -> m [K]
typeCheck ctx t tyT = do
  h <- join $ pick "Head" $ heads ctx
  (kEqDC t (RHSHead h) :) <$> typeCheck' ctx tyT h

heads :: (WithParams, MonadSoup m) => Ctx -> [(L, m (DCore_ Soup))]
heads ctx =
  [ (L "*", return Star)
  , (L "v", pickVar ctx <&> \x -> Var x)
  , (L "Π", pick' "Rel" [Rel, Irr] >>= \rel -> freshes <&> \(tyA, tyB) -> Pi rel () tyA tyB)
  , (L "λ", pick' "Rel" [Rel, Irr] >>= \rel -> freshes <&> \(tyA, b) -> Abs rel () tyA b)
  , (L ";", pick' "Rel" [Rel, Irr] >>= \rel -> freshes <&> \(b, a) -> App b a rel)
  ] ++
  [ (L "f", Fun <$> pick' "Constant" [minBound .. maxBound])
  | not noConstants
  ] ++
  (guard coercions *>
  [ (L "Π'", fresh_ CoPi)
  , (L "λ'", fresh_ CoAbs)
  , (L ";'", fresh_ CoApp)
  , (L ":>", fresh_ Coerce)
  ])
  where
    (<&>) :: Functor f => f a -> (a -> b) -> f b
    (<&>) = flip fmap

headsC :: (WithParams, MonadSoup m) => Ctx -> [(L, m (Coercion_ Soup))]
headsC ctx =
  [ (L "CVar", pickCVar ctx <&> \x -> CVar x)
  , (L "CRefl", fresh_ CRefl)
  , (L "CRefl'", fresh_ CRefl')
  , (L "CSym", fresh_ CSym)
  , (L "CSeq", fresh_ CSeq)
  , (L "CRed", fresh_ CRed)
  , (L "CPi", pick' "Rel" [Rel, Irr] >>= \rel -> fresh_ (CPi rel))
  , (L "CAbs", pick' "Rel" [Rel, Irr] >>= \rel -> fresh_ (CAbs rel))
  , (L "CApp", pick' "Rel" [Rel, Irr] >>= \rel -> freshes <&> \(b, a) -> CApp b a rel)
  , (L "CCoAbs", fresh_ CCoAbs)
  , (L "CCoPi", fresh_ CCoPi)
  , (L "CCoApp", fresh_ CCoApp)
  ]

fresh_ :: (FunConstraints t Fresh, MonadFresh m) => t -> m (Result t)
fresh_ = createA_ (For :: For Fresh) fresh

typeCheck' :: MonadSoup m => Ctx -> DCId -> DCore_ Soup -> m [K]
typeCheck' _ctx tyT Star = do
  return
    [ kEqDC tyT (RHSHead Star)
    ]

typeCheck' _ctx tyT (Fun c) = case c of
  Nat      -> return [ kEqDC tyT (RHSHead Star) ]
  Zero     -> return [ kEqDC tyT (RHSHead (Fun Nat)) ]
  Succ     -> return [ kEqDC tyT (RHSHead natToNatTyDC) ]
  FoldNat  -> return [ kEqDC tyT (RHSId foldNatTy0 0) ]

typeCheck' ctx tyT (Var x) = do
  case lookupVar x ctx of
    Nothing -> MonadFail.fail "Unbound variable"
    Just ty ->
      return
        [ kEqDC tyT (RHSId ty (asShift x + 1))
        ]

typeCheck' ctx tyStar (Pi _ () tyA tyB) = do
  let ctx' = insertVar tyA ctx
  return
    [ kEqDC tyStar (RHSHead Star)
    , KType ctx' tyB tyStar
    , KWF ctx'
    , K_ (KType ctx tyA tyStar)
    ]

typeCheck' ctx tyT (Abs rel () tyA b) = do
  (tyB, tyStar) <- freshes
  let ctx' = insertVar tyA ctx
  return
    [ kEqDC tyT (RHSHead (Pi rel () tyA tyB))
    , KType ctx' b tyB
    , KWF ctx'
    , KRel rel b
    , K_ (kEqDC tyStar (RHSHead Star))
    , K_ (KType ctx tyA tyStar)
    ]

typeCheck' ctx tyT (App b a rel) = do
  (tyA, ty', tyB) <- freshes
  return
    [ kEqDC tyB (RHSHead (Pi rel () tyA ty'))
    , kEqDC tyT (RHSSub ty' a)
    , KType ctx b tyB
    , KType ctx a tyA
    ]

typeCheck' ctx tyB (Coerce a g) = do
  (tyA, tyStar) <- freshes
  return
    [ kEqDC tyStar (RHSHead Star)
    , KType ctx tyB tyStar
    , KType ctx a tyA
    , KTypeC ctx (cctx ctx) g (tyA :~: tyB)
    ]

typeCheck' ctx tyStar (CoPi () phi tyB) = do
  let ctx' = insertCVar phi ctx
  return
    [ kEqDC tyStar (RHSHead Star)
    , KType ctx' tyB tyStar
    , KWF ctx'
    , K_ (KOK ctx phi)
    ]

typeCheck' ctx tyT (CoAbs () phi b) = do
  tyB <- fresh
  let ctx' = insertCVar phi ctx
  return
    [ kEqDC tyT (RHSHead (CoPi () phi tyB))
    , KType ctx' b tyB
    , KWF ctx'
    , K_ (KOK ctx phi)
    ]

typeCheck' ctx tyT (CoApp a g) = do
  (phi, tyB, ty') <- freshes
  return
    [ kEqDC ty' (RHSHead (CoPi () phi tyB))
    , kEqDC tyT (RHSSubC g tyB)
    , KType ctx a ty'
    , KTypeC ctx (cctx ctx) g phi
    ]

typeCheckC' :: MonadSoup m => Ctx -> Ctx' -> EqProp DCId -> Coercion_ Soup -> m [K]
typeCheckC' ctx _cctx (a :~: b) (CVar v) =
  case lookupCVar v ctx of
    Nothing -> MonadFail.fail "Unbound c-variable"
    Just (a' :~: b') ->
      return
        [ kEqDC a (RHSId a' (asShift v + 1))
        , kEqDC b (RHSId b' (asShift v + 1))
        ]

typeCheckC' ctx _cctx (a :~: b) (CRefl a') = do
  tyA <- fresh
  return
    [ kEqDC a (RHSId a' 0)
    , kEqDC b (RHSId a' 0)
    , K_ (KType ctx a' tyA)
    ]

typeCheckC' ctx cctx (a :~: b) (CSym g) =
  return
    [ KTypeC ctx cctx g (b :~: a)
    ]

typeCheckC' ctx cctx (a :~: c) (CSeq g1 g2) = do
  b <- fresh
  return
    [ KTypeC ctx cctx g1 (a :~: b)
    , KTypeC ctx cctx g2 (b :~: c)
    ]

typeCheckC' ctx cctx (ty1 :~: ty2) (CAbs rel () ga gb) = do
  (tyA1, tyA2, b1, b2, b3, tyStar) <- freshes
  let ctx' = insertVar tyA1 ctx
  return
    [ kEqDC ty1 (RHSHead (Abs rel () tyA1 b1))
    , kEqDC ty2 (RHSHead (Abs rel () tyA2 b3))
    , KRel rel b1
    , KRel rel b3
    , KTypeC ctx cctx ga (tyA1 :~: tyA2)
    , KTypeC ctx' cctx gb (b1 :~: b2)
    , K_ (KType ctx tyA2 tyStar)
    , kEqDC tyStar (RHSHead Star)
    , error "eqSub" b3 b2 (error "{x :> sym g1 / x}")
    ]

initK :: MonadSoup m => m ([K], DCId, DCId)
initK = do
  (t, ty) <- freshes
  return
    ([KType emptyCtx t ty], t, ty)

--

data S h = S
  { counter :: !Integer
  , constraints :: h
  } deriving (Generic, Show)

newtype Skip (t :: (* -> *) -> * -> *) (m :: * -> *) a
  = Skip { unSkip :: t m a }
  deriving (Functor, Applicative, Monad)

instance MonadPlus m => Alternative (Skip (ExceptT e) m) where
  empty = Skip (ExceptT empty)
  Skip (ExceptT a) <|> Skip (ExceptT b) = Skip (ExceptT (a <|> b))

instance MonadPlus m => MonadPlus (Skip (ExceptT e) m)

isKType :: K -> Bool
isKType (KType{}) = True
isKType _ = False

focus :: [a] -> [(a, [a])]
focus = focus' []
  where
    focus' _ [] = []
    focus' aux (a : as) = (a, aux ++ as) : focus' (a : aux) as

size :: Foldable f => Cofree f a -> Integer
size = getSum . size'
  where size' (_ :< f) = 1 + foldMap size' f

class Lns (n :: Symbol) s a | n s -> a where
  l :: Lens' s a

instance Lns "ks" (S h) h where
  l f s = fmap (\h -> s { constraints = h }) (f (constraints s))

showDCoreSoup_ :: WithParams => (Int -> DCId -> String) -> Int -> DCore_ Soup -> String
showDCoreSoup_ showDCId n t = case t of
  Star -> "*"
  Fun c -> show c
  Var n -> showDeBruijnV n
  App t u rel ->
    parensIf (n >= 11) $
      showDCId 10 t ++ " " ++ showRel rel " " ++ showDCId 11 u
  Pi rel () u v ->
    parensIf (n >= 0) $
      "Π" ++ showRel rel "" ++ " " ++ showDCId 11 u ++ " -> " ++ showDCId (-1) v
  Abs rel () u v ->
    parensIf (n >= 0) $
      "λ" ++ showRel rel "" ++ " " ++ showDCId 11 u ++ " . " ++ showDCId (-1) v

showDCoreSoup :: WithParams => DCore_ Soup -> String
showDCoreSoup = showDCoreSoup_ (const show) 0

parensIf :: Bool -> String -> String
parensIf True s = parens s
parensIf False s = s

showDeBruijnV :: DeBruijnV -> String
showDeBruijnV (DeBruijnV x) = "i" ++ show x

showRel :: WithParams => Rel -> String -> String
showRel _ | not relevance = id
showRel Rel = ("+" ++)
showRel Irr = ("-" ++)

parens :: String -> String
parens s = "(" ++ s ++ ")"
