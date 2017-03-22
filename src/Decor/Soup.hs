{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Decor.Soup where

import Control.Monad.Except
import Control.Monad.State.Strict

import Control.Comonad.Cofree

import Generics.OneLiner
import GHC.Generics (Generic)

import Decor.Types

data Soup

type instance RelT Soup = Rel
type instance FunT Soup = FunId
type instance VarT Soup = VarId
type instance BindVarT Soup = VarId
type instance CVarT Soup = VarId
type instance BindCVarT Soup = CVarId
type instance DCore Soup = DCId
type instance Coercion Soup = CoercionId

newtype DCId = DCId Integer
  deriving (Eq, Ord, Show)

newtype CoercionId = CoercionId Integer
  deriving (Eq, Ord, Show)

-- | Constraints.
data K where
  KEqDC :: DCId -> RHS -> K
  -- ^ @t = u@. Term equality.

  KType :: Ctx -> DCId -> DCId -> K
  -- ^ @G |- t : u@. Typing judgement.

  KTypeC :: Ctx -> Ctx' -> CoercionId -> EqProp DCId -> K
  -- ^ @G |- g : a ~ b@. Coercion typing judgement.

  KRel :: Rel -> VarId -> DCId -> K
  -- ^ @r & x <- |t|@. Relevance check.

  KWF :: Ctx -> K
  -- ^ @|- G@. Well-formed context.

  KOK :: Ctx -> EqProp DCId -> K
  -- ^ @G |- phi OK@. Well-formed equality proposition.

  K_ :: K -> K
  -- ^ Redundant constraints.

  deriving (Eq, Ord, Show)

data RHS
  = RHSId DCId
  | RHSHead (DCore_ Soup)
  | RHSSub VarId DCId DCId
  | RHSSubC CVarId CoercionId DCId
  deriving (Eq, Ord, Show)

class (Monad m, Fresh m Integer) => MonadSoup m where
  pick :: [a] -> m a

class Applicative m => Fresh m a where
  fresh :: m a

instance (Applicative m, Fresh m Integer) => Fresh m VarId where
  fresh = VarId <$> fresh

instance (Applicative m, Fresh m Integer) => Fresh m CVarId where
  fresh = CVarId <$> fresh

instance (Applicative m, Fresh m Integer) => Fresh m DCId where
  fresh = DCId <$> fresh

instance (Applicative m, Fresh m Integer) => Fresh m CoercionId where
  fresh = CoercionId <$> fresh

instance (Applicative m, Fresh m a) => Fresh m (EqProp a) where
  fresh = (:~:) <$> fresh <*> fresh

freshes
  :: forall t m
  .  (Generic t, ADTRecord t, Constraints t (Fresh m), Applicative m)
  => m t
freshes = createA' (For :: For (Fresh m)) fresh

data Ctx = Ctx
  { varCtx :: [(VarId, DCId)]
  , cVarCtx :: [(CVarId, EqProp DCId)]
  } deriving (Eq, Ord, Show)

emptyCtx :: Ctx
emptyCtx = Ctx [] []

data Ctx' = Ctx' [CVarId]
  deriving (Eq, Ord, Show)

cctx :: Ctx -> Ctx'
cctx ctx = Ctx' [c | (c, _) <- cVarCtx ctx]

pickVar :: MonadSoup m => Ctx -> m (VarId, DCId)
pickVar ctx = pick (varCtx ctx)

insertVar :: VarId -> DCId -> Ctx -> Ctx
insertVar x ty ctx = ctx { varCtx = (x, ty) : varCtx ctx }

insertCVar :: CVarId -> EqProp DCId -> Ctx -> Ctx
insertCVar c phi ctx = ctx { cVarCtx = (c, phi) : cVarCtx ctx }

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
    [ KEqDC t (RHSHead Star)
    , KEqDC tyT (RHSHead Star)
    ]

tcVar ctx t tyT = do
  (x, ty) <- pickVar ctx
  return
    [ KEqDC t (RHSHead (Var x))
    , KEqDC tyT (RHSId ty)
    ]

tcPi ctx t tyStar = do
  rel <- pick [Rel, Irr]
  (x, tyA, tyB) <- freshes
  let ctx' = insertVar x tyA ctx
  return
    [ KEqDC t (RHSHead (Pi rel x tyA tyB))
    , KEqDC tyStar (RHSHead Star)
    , KType ctx' tyB tyStar
    , KWF ctx'
    , K_ (KType ctx tyA tyStar)
    ]

tcAbs ctx t tyT = do
  rel <- pick [Rel, Irr]
  (x, tyA, b, tyB, tyStar) <- freshes
  let ctx' = insertVar x tyA ctx
  return
    [ KEqDC t (RHSHead (Abs rel x tyA b))
    , KEqDC tyT (RHSHead (Pi rel x tyA tyB))
    , KType ctx' b tyB
    , KWF ctx'
    , KRel rel x b
    , K_ (KEqDC tyStar (RHSHead Star))
    , K_ (KType ctx tyA tyStar)
    ]

tcApp ctx t tyT = do
  rel <- pick [Rel, Irr]
  (b, a, x, tyA, ty', tyB) <- freshes
  return
    [ KEqDC t   (RHSHead (App b a rel))
    , KEqDC tyB (RHSHead (Pi rel x tyA ty'))
    , KEqDC tyT (RHSSub x a ty')
    , KType ctx b tyB
    , KType ctx a tyA
    ]

tcConv ctx t tyB = do
  (a, g, tyA, tyStar) <- freshes
  return
    [ KEqDC t (RHSHead (Coerce a g))
    , KEqDC tyStar (RHSHead Star)
    , KType ctx tyB tyStar
    , KType ctx a tyA
    , KTypeC ctx (cctx ctx) g (tyA :~: tyB)
    ]

tcCoPi ctx t tyStar = do
  (c, phi, tyB) <- freshes
  let ctx' = insertCVar c phi ctx
  return
    [ KEqDC t (RHSHead (CoPi c phi tyB))
    , KEqDC tyStar (RHSHead Star)
    , KType ctx' tyB tyStar
    , KWF ctx'
    , K_ (KOK ctx phi)
    ]

tcCoAbs ctx t tyT = do
  (c, phi, b, tyB) <- freshes
  let ctx' = insertCVar c phi ctx
  return
    [ KEqDC t   (RHSHead (CoAbs c phi b))
    , KEqDC tyT (RHSHead (CoPi c phi tyB))
    , KType ctx' b tyB
    , KWF ctx'
    , K_ (KOK ctx phi)
    ]

tcCoApp ctx t tyT = do
  (a, g, c, phi, tyB, ty') <- freshes
  return
    [ KEqDC t   (RHSHead (CoApp a g))
    , KEqDC tyT (RHSSubC c g tyB)
    , KEqDC ty' (RHSHead (CoPi c phi tyB))
    , KType ctx a ty'
    , KTypeC ctx (cctx ctx) g phi
    ]

initK :: MonadSoup m => m ([K], DCId, DCId)
initK = do
  (t, ty) <- freshes
  return
    ([KType emptyCtx t ty], t, ty)

-- Names that can't possibly be confused with local variables.
m_T0, m_Ty0 :: DCId
m_S0 :: S

ExceptT [Right ((m_T0, m_Ty0), m_S0)] =
  ((`runStateT` s) . unM)
    (initK >>= \(ks, t, ty) -> andK ks >> return (t, ty))
  where s = S 0 []

--

data S = S
  { counter :: !Integer
  , constraints :: [K]
  } deriving Show

type ForkF = ExceptT () []

newtype M a = M { unM :: StateT S ForkF a }
  deriving (Functor, Applicative, Monad)

instance Fresh M Integer where
  fresh = M . state $ \s ->
    let i = counter s in (i, s {counter = i+1})

instance MonadSoup M where
  pick = M . lift . lift

runM :: M [K] -> S -> ForkF S
runM = execStateT . unM . (>>= andK)

andK :: [K] -> M ()
andK ks = M . modify' $ \s -> s {constraints = ks ++ constraints s}

extractKType :: (Ctx -> DCId -> DCId -> M a) -> M a
extractKType k = M $ do
  s <- get
  case break isKType (constraints s) of
    (cs, KType ctx t ty : cs') -> do
      put (s { constraints = cs ++ cs' })
      unM (k ctx t ty)
    _ -> (lift . lift) []
  where
    isKType (KType{}) = True
    isKType _ = False

tree :: Cofree ForkF S
tree = coiter (runM (extractKType typeCheck)) m_S0

data Elide f a = X | Y (f a)
  deriving (Eq, Ord, Show, Functor)

takeDepth :: Int -> Cofree ForkF a -> Cofree (Elide ForkF) a
takeDepth n (a :< f) = a :< takeDepth' n f
  where
    takeDepth' 0 _ = X
    takeDepth' n f = Y (fmap (takeDepth (n - 1)) f)

tree' :: Cofree (Elide ForkF) S
tree' = takeDepth 2 tree
