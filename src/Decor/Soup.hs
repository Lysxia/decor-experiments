{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
import Control.Monad.State.Strict
import Control.Monad.Writer

import Control.Comonad.Cofree

import Data.Foldable

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap

import Lens.Micro.Platform

import Generics.OneLiner
import GHC.Generics (Generic)
import GHC.TypeLits

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
  deriving (Eq, Ord, Show, Num)

shift :: DeBruijnV -> Shift -> DeBruijnV
shift v s = v + DeBruijnV s

asShift :: DeBruijnV -> Shift
asShift (DeBruijnV i) = i

newtype DeBruijnC = DeBruijnC Integer
  deriving (Eq, Ord, Show, Num)

newtype DCId = DCId Integer
  deriving (Eq, Ord, Show)

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

class (Monad m, MonadFresh m) => MonadSoup m where
  pick :: [a] -> m a

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
cctx ctx = Ctx' (fromIntegral <$> [0 .. length (cVarCtx ctx)])

pickVar :: MonadSoup m => Ctx -> m (DeBruijnV, DCId)
pickVar ctx = pick (zip (DeBruijnV <$> [0 ..]) (varCtx ctx))

insertVar :: DCId -> Ctx -> Ctx
insertVar ty ctx = ctx { varCtx = ty : varCtx ctx }

insertCVar :: EqProp DCId -> Ctx -> Ctx
insertCVar phi ctx = ctx { cVarCtx = phi : cVarCtx ctx }

alternate3 :: MonadSoup m => [a -> b -> c -> m d] -> a -> b -> c -> m d
alternate3 fs a b c = pick fs >>= \f -> f a b c

typeCheck :: MonadSoup m => Ctx -> DCId -> DCId -> m [K]
typeCheck = alternate3
  [ tcStar
  , tcVar
  , tcPi
  , tcAbs
  , tcApp
  ]

tcStar, tcVar, tcPi, tcAbs, tcApp, tcConv, tcCoPi,
  tcCoAbs, tcCoApp
  :: MonadSoup m => Ctx -> DCId -> DCId -> m [K]

tcStar _ctx t tyT = do
  return
    [ kEqDC t (RHSHead Star)
    , kEqDC tyT (RHSHead Star)
    ]

tcVar ctx t tyT = do
  (x, ty) <- pickVar ctx
  return
    [ kEqDC t (RHSHead (Var x))
    , kEqDC tyT (RHSId ty (asShift x + 1))
    ]

tcPi ctx t tyStar = do
  rel <- pick [Rel, Irr]
  (tyA, tyB) <- freshes
  let ctx' = insertVar tyA ctx
  return
    [ kEqDC t (RHSHead (Pi rel () tyA tyB))
    , kEqDC tyStar (RHSHead Star)
    , KType ctx' tyB tyStar
    , KWF ctx'
    , K_ (KType ctx tyA tyStar)
    ]

tcAbs ctx t tyT = do
  rel <- pick [Rel, Irr]
  (tyA, b, tyB, tyStar) <- freshes
  let ctx' = insertVar tyA ctx
  return
    [ kEqDC t (RHSHead (Abs rel () tyA b))
    , kEqDC tyT (RHSHead (Pi rel () tyA tyB))
    , KType ctx' b tyB
    , KWF ctx'
    , KRel rel b
    , K_ (kEqDC tyStar (RHSHead Star))
    , K_ (KType ctx tyA tyStar)
    ]

tcApp ctx t tyT = do
  rel <- pick [Rel, Irr]
  (b, a, tyA, ty', tyB) <- freshes
  return
    [ kEqDC t   (RHSHead (App b a rel))
    , kEqDC tyB (RHSHead (Pi rel () tyA ty'))
    , kEqDC tyT (RHSSub a ty')
    , KType ctx b tyB
    , KType ctx a tyA
    ]

tcConv ctx t tyB = do
  (a, g, tyA, tyStar) <- freshes
  return
    [ kEqDC t (RHSHead (Coerce a g))
    , kEqDC tyStar (RHSHead Star)
    , KType ctx tyB tyStar
    , KType ctx a tyA
    , KTypeC ctx (cctx ctx) g (tyA :~: tyB)
    ]

tcCoPi ctx t tyStar = do
  (phi, tyB) <- freshes
  let ctx' = insertCVar phi ctx
  return
    [ kEqDC t (RHSHead (CoPi () phi tyB))
    , kEqDC tyStar (RHSHead Star)
    , KType ctx' tyB tyStar
    , KWF ctx'
    , K_ (KOK ctx phi)
    ]

tcCoAbs ctx t tyT = do
  (phi, b, tyB) <- freshes
  let ctx' = insertCVar phi ctx
  return
    [ kEqDC t   (RHSHead (CoAbs () phi b))
    , kEqDC tyT (RHSHead (CoPi () phi tyB))
    , KType ctx' b tyB
    , KWF ctx'
    , K_ (KOK ctx phi)
    ]

tcCoApp ctx t tyT = do
  (a, g, phi, tyB, ty') <- freshes
  return
    [ kEqDC t   (RHSHead (CoApp a g))
    , kEqDC ty' (RHSHead (CoPi () phi tyB))
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
  } deriving Show

type ForkF = ExceptT () []

newtype M h a = M { unM :: M' h a }
  deriving (Functor, Applicative, Monad, MonadState (S h))

type M' h = StateT (S h) ForkF

instance MonadFresh (M h) where
  freshI = state $ \s ->
    let i = counter s in (i, s {counter = i+1})

instance MonadSoup (M h) where
  pick = M . lift . lift

runM :: KStore h => M h [K] -> S h -> ForkF (S h)
runM = execStateT . unM . (>>= andKs)

class KStore h where
  initStore :: h
  andK :: K -> M h ()
  reduce :: M h ()
  extractKType :: (Ctx -> DCId -> DCId -> M h a) -> M h a

  andKs :: KStore h => [K] -> M h ()
  andKs = traverse_ andK


generate :: KStore h => (Cofree ForkF (S h), (DCId, DCId))
generate = (coiter (runM (extractKType typeCheck)) s0, tt0)
  where
    ExceptT [Right (tt0, s0)] =
      ((`runStateT` s) . unM)
        (initK >>= \(ks, t, ty) -> andKs ks >> reduce >> return (t, ty))
    s = S 0 initStore

tree :: KStore h => Cofree ForkF (S h)
tree = fst generate

data Elide f a = X | Y (f a)
  deriving (Eq, Ord, Show, Foldable, Functor)

takeDepth :: Int -> Cofree ForkF a -> Cofree (Elide ForkF) a
takeDepth n (a :< f) = a :< takeDepth' n f
  where
    takeDepth' 0 _ = X
    takeDepth' n f = Y (fmap (takeDepth (n - 1)) f)

isKType :: K -> Bool
isKType (KType{}) = True
isKType _ = False

focus :: [a] -> [(a, [a])]
focus = focus' []
  where
    focus' _ [] = []
    focus' aux (a : as) = (a, aux) : focus' (a : aux) as

size :: Foldable f => Cofree f a -> Integer
size = getSum . size'
  where size' (_ :< f) = 1 + foldMap size' f

class L (n :: Symbol) s a | n s -> a where
  l :: Lens' s a

instance L "ks" (S h) h where
  l f s = fmap (\h -> s { constraints = h }) (f (constraints s))
