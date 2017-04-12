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
import Control.Monad
import Control.Monad.Except
import Control.Monad.Fail as MonadFail
import Control.Monad.Writer

import Control.Comonad.Cofree

import Data.List (elemIndex)
import Data.Maybe
import Data.Typeable

import Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap

import Lens.Micro.Platform

import Generics.OneLiner
import GHC.Generics (Generic)
import GHC.TypeLits

import qualified Decor.Parser as P
import Decor.Types

data Soup

type instance RelT Soup = Rel
type instance FunT Soup = FunId
type instance VarT Soup = DeBruijnV
type instance BindVarT Soup = ()
type instance CVarT Soup = DeBruijnC
type instance BindCVarT Soup = ()
type instance DCore Soup = DCId
type instance Coercion Soup = CoercionId

newtype DeBruijnV = DeBruijnV Integer
  deriving (Eq, Ord, Show, Enum)

shift :: DeBruijnV -> Shift -> DeBruijnV
shift (DeBruijnV i) s = DeBruijnV (i + s)

asShift :: DeBruijnV -> Shift
asShift (DeBruijnV i) = i

newtype DeBruijnC = DeBruijnC Integer
  deriving (Eq, Ord, Show, Enum)

newtype DCId = DCId Integer
  deriving (Eq, Ord)

instance Show DCId where
  show (DCId n) = "u" ++ show n

newtype CoercionId = CoercionId Integer
  deriving (Eq, Ord, Show)

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
  , _noPruning :: Bool
  , _iniTerm :: P.DCore
  , _iniType :: P.DCore
  } deriving Generic

ini :: MonadSoup m => DCId -> P.DCore -> m [K]
ini = ini' []

ini' :: MonadSoup m => [String] -> DCId -> P.DCore -> m [K]
ini' _ _ Nothing = return []
ini' ctx t (Just t_) = case t_ of
  Star -> return [KEqDC t (RHSHead Star)]

  Var v
    | Just i <- elemIndex v ctx -> return [KEqDC t (RHSHead (Var (DeBruijnV (fromIntegral i))))]
    | otherwise -> MonadFail.fail $ "Unbound: " ++ v

  Pi rel v t1_ t2_ -> do
    (t1, t2) <- freshes
    k1 <- ini' ctx t1 t1_
    k2 <- ini' (v : ctx) t2 t2_
    return (KEqDC t (RHSHead (Pi rel () t1 t2)) : k1 ++ k2)

  Abs rel v t1_ t2_ -> do
    (t1, t2) <- freshes
    k1 <- ini' ctx t1 t1_
    k2 <- ini' (v : ctx) t2 t2_
    return (KEqDC t (RHSHead (Abs rel () t1 t2)) : k1 ++ k2)

  App t1_ t2_ rel -> do
    (t1, t2) <- freshes
    k1 <- ini' ctx t1 t1_
    k2 <- ini' ctx t2 t2_
    return (KEqDC t (RHSHead (App t1 t2 rel)) : k1 ++ k2)

type WithParams = (?params :: Params)

showEqualities :: WithParams => Bool
showEqualities = _showEqualities ?params

relevance :: WithParams => Bool
relevance = _relevance ?params

boring :: WithParams => Bool
boring = _boring ?params

absurd :: WithParams => Bool
absurd = _absurd ?params

noPruning :: WithParams => Bool
noPruning = _noPruning ?params

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

type Shift = Integer

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

freshes
  :: forall t m
  .  (Generic t, ADTRecord t, Constraints t Fresh, MonadFresh m)
  => m t
freshes = createA' (For :: For Fresh) fresh

data Ctx = Ctx
  { varCtx :: [DCId]
  , cVarCtx :: [EqProp DCId]
  } deriving (Eq, Ord, Show)

emptyCtx :: Ctx
emptyCtx = Ctx [] []

data Ctx' = Ctx' [DeBruijnC]
  deriving (Eq, Ord, Show)

cctx :: Ctx -> Ctx'
cctx ctx = Ctx' (toEnum <$> [0 .. length (cVarCtx ctx)])

pickVar :: MonadSoup m => Ctx -> m DeBruijnV
pickVar ctx = pick' "Var" (toEnum <$> [0 .. length (varCtx ctx) - 1])

lookupVar :: DeBruijnV -> Ctx -> Maybe DCId
lookupVar (DeBruijnV n) ctx = listToMaybe $ drop (fromIntegral n) (varCtx ctx)

insertVar :: DCId -> Ctx -> Ctx
insertVar ty ctx = ctx { varCtx = ty : varCtx ctx }

insertCVar :: EqProp DCId -> Ctx -> Ctx
insertCVar phi ctx = ctx { cVarCtx = phi : cVarCtx ctx }

typeCheck :: MonadSoup m => Ctx -> DCId -> DCId -> m [K]
typeCheck ctx t tyT = pick "Head"
  [ (L "*", return Star)
  , (L "v", pickVar ctx <&> \x -> Var x)
  , (L "Π", pick' "Rel" [Rel, Irr] >>= \rel -> freshes <&> \(tyA, tyB) -> Pi rel () tyA tyB)
  , (L "λ", pick' "Rel" [Rel, Irr] >>= \rel -> freshes <&> \(tyA, b) -> Abs rel () tyA b)
  , (L ";", pick' "Rel" [Rel, Irr] >>= \rel -> freshes <&> \(b, a) -> App b a rel)
  ] >>= \h_ -> h_ >>= \h -> (kEqDC t (RHSHead h) :) <$> typeCheck' ctx tyT h
  where
    (<&>) :: Functor f => f a -> (a -> b) -> f b
    (<&>) = flip fmap

typeCheck' :: MonadSoup m => Ctx -> DCId -> DCore_ Soup -> m [K]
typeCheck' _ctx tyT Star = do
  return
    [ kEqDC tyT (RHSHead Star)
    ]

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
