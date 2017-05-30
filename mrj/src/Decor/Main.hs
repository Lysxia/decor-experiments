
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Decor.Main where

import GHC.Exts (Constraint)
import Generics.OneLiner

import Control.Applicative
import Control.Monad
import Data.Foldable

import qualified Data.Map as Map
import Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap

import Decor.Gen
import Decor.Types

newVar :: MonadGen m => m VarId
newVar = VarId <$> newInteger

newCVar :: MonadGen m => m CVarId
newCVar = CVarId <$> newInteger

data Partial (f :: *) (r :: * -> *)

type instance VarT      (Partial f r) = VarId
type instance BindVarT  (Partial f r) = VarId
type instance FunT      (Partial f r) = f
type instance CVarT     (Partial f r) = CVarId
type instance BindCVarT (Partial f r) = CVarId
type instance RelT      (Partial f r) = Rel
type instance DCore     (Partial f r) = r (DCore_ (Partial f r))
type instance Coercion  (Partial f r)
  = TODO
  -- = r (Coercion_ (Partial f r))

data TODO = TODO
  deriving (Eq, Show)

type Simple m p =
  ( DCore p ~ URef m (DCore_ p)
  , VarT p ~ VarId
  , BindVarT p ~ VarId
  , RelT p ~ Rel
  , CVarT p ~ CVarId
  , BindCVarT p ~ CVarId
  )

data UnifyCtx = UnifyCtx
  { varUnifyCtx :: Bimap VarId VarId
  , cVarUnifyCtx :: Bimap CVarId CVarId
  }

emptyUnifyCtx :: UnifyCtx
emptyUnifyCtx = UnifyCtx Bimap.empty Bimap.empty

class MonadGen m => Unifiable m a where
  unify :: UnifyCtx -> a -> a -> m ()
  weakUnify :: UnifyCtx -> a -> a -> m ()
  shallowCopy :: a -> m a

unifyPhi :: Unifiable m a => UnifyCtx -> EqProp a -> EqProp a -> m ()
unifyPhi ctx (a :~: b) (a' :~: b') = unify ctx a a' *> unify ctx b b'

instance Unifiable m a => Unifiable m (URef m a) where
  unify uctx r s = do
    ma <- getRef r
    mb <- getRef s
    for_ ma $ \ a ->
      for_ mb $ \ b ->
        unify uctx a b
    mergeRef r s

  weakUnify uctx r s = do
    bindRef r $ \ a -> do
      mb <- getRef s
      b <- case mb of
        Just b -> return b
        Nothing -> shallowCopy a
      weakUnify uctx a b

  shallowCopy _ = newRef

instance MonadGen m => Unifiable m VarId where
  unify uctx v v' =
    case Bimap.lookup v (varUnifyCtx uctx) of
      Nothing | v == v' -> return ()
      Just v_ | v_ == v' -> return ()
      _ -> empty

instance MonadGen m => Unifiable m CVarId where
  unify uctx c c' =
    case Bimap.lookup c (cVarUnifyCtx uctx) of
      Nothing | c == c' -> return ()
      Just c_ | c_ == c' -> return ()
      _ -> empty

instance
  ( MonadGen m
  , Fields Unifiable m p
  , BindVarT p ~ VarId
  , BindCVarT p ~ CVarId
  ) => Unifiable m (DCore_ p) where
  unify uctx (Abs rel x a b) (Abs rel' x' a' b') = do
    unify uctx rel rel'
    unify uctx a a'
    unify (uctx { varUnifyCtx = Bimap.insert x x' $ varUnifyCtx uctx }) b b'
  unify uctx (Pi rel x a b) (Pi rel' x' a' b') = do
    unify uctx rel rel'
    unify uctx a a'
    unify (uctx { varUnifyCtx = Bimap.insert x x' $ varUnifyCtx uctx }) b b'
  unify uctx (CoAbs x a b) (CoAbs x' a' b') = do
    unifyPhi uctx a a'
    unify (uctx { cVarUnifyCtx = Bimap.insert x x' $ cVarUnifyCtx uctx }) b b'
  unify uctx (CoPi x a b) (CoPi x' a' b') = do
    unifyPhi uctx a a'
    unify (uctx { cVarUnifyCtx = Bimap.insert x x' $ cVarUnifyCtx uctx }) b b'
  unify uctx t t' = unAM
    (mzipWith
      (For :: For (Unifiable m))
      (\i j -> AM (unify uctx i j))
      t
      t')

  shallowCopy =
    gtraverse
      (For :: For (Unifiable m))
      shallowCopy

instance Unifiable m a => Unifiable m (EqProp a) where
  unify u (a :~: b) (a' :~: b') = unify u a a' *> unify u b b'

  weakUnify u (a :~: b) (a' :~: b') = weakUnify u a a' *> weakUnify u b b'

  shallowCopy (a :~: b) = liftA2 (:~:) (shallowCopy a) (shallowCopy b)

newtype AM m = AM { unAM :: m () }

instance Applicative m => Monoid (AM m) where
  mempty = AM (pure ())
  mappend (AM a) (AM b) = AM (a *> b)

type Fields (c :: (* -> *) -> * -> Constraint) m p =
  ( c m (VarT p)
  , c m (FunT p)
  , c m (RelT p)
  , c m (DCore p)
  , c m (CVarT p)
  , c m (Coercion p)
  )

(%) :: a -> b -> (a, b)
(%) = (,)

data Ctx p = Ctx
  { refCtx :: RecCtx p
  , varCtx :: VarCtx p
  , cVarCtx :: CVarCtx p
  }

type RecCtx p = Map.Map (FunT p) (DCore p)
type VarCtx p = [(Rel, VarId, DCore p)]
type CVarCtx p = [(CVarId, EqProp (DCore p))]

pushVar :: Rel -> VarId -> DCore p -> Ctx p -> Ctx p
pushVar rel v ty ctx = ctx { varCtx = (rel, v, ty) : varCtx ctx }

pushCVar :: CVarId -> EqProp (DCore p) -> Ctx p -> Ctx p
pushCVar c phi ctx = ctx { cVarCtx = (c, phi) : cVarCtx ctx }

type Generator m p
  =  ( MonadGen m
     , Simple m p
     , Unifiable m (DCore_ p)
     )
  => Ctx p
  -> DCore p  -- ^ Term
  -> DCore p  -- ^ Type
  -> m ()

data D m p = D
  { unifyD  :: Ctx p -> DCore p -> DCore_ p -> m ()
  , strict  :: Ctx p -> DCore p -> DCore p -> m ()
  , lazy    :: Ctx p -> DCore p -> DCore p -> m ()
  , strictC :: Ctx p -> Coercion p -> EqProp (DCore p) -> m ()
  , subst
      :: Ctx p    -- Gamma
      -> VarId    -- x
      -> DCore p  -- a
      -> DCore p  -- A
      -> DCore p  -- B
      -> DCore p  -- B[a/x]
      -> m ()
  , substC
      :: Ctx p
      -> CVarId
      -> Coercion p
      -> EqProp (DCore p)
      -> DCore p  -- B
      -> DCore p  -- B[g/c]
      -> m ()
  }

type Generator' m p
  =  ( MonadGen m
     , Simple m p
     , Unifiable m (DCore_ p)
     )
  => D m p
  -> Ctx p
  -> DCore_ p  -- ^ Term
  -> DCore p   -- ^ Type
  -> m ()

type Generator'_ m p
  =  ( MonadGen m
     , Simple m p
     , Unifiable m (DCore_ p)
     )
  => D m p
  -> Ctx p
  -> DCore p   -- ^ Type
  -> DCore_ p  -- ^ Term
  -> m ()

typeCheck :: Generator' m p
typeCheck d ctx tx ty = typeCheck' d ctx ty tx

typeCheck' :: Generator'_ m p
typeCheck' d ctx ty Star = unifyD d ctx ty Star
typeCheck' d ctx ty (Var v) = guard (ctxCheck v (varCtx ctx))
typeCheck' d ctx tyStar (Pi rel v tyA tyB) = do
  unifyD d ctx tyStar Star
  lazy   d   ctx tyA tyStar
  strict d v_ctx tyB tyStar
  where
    v_ctx = pushVar rel v tyA ctx
typeCheck' d ctx ty (Abs rel v tyA b) = do
  star <- ref Star
  tyB <- newRef
  unifyD d ctx ty (Pi rel v tyA tyB)
  lazy   d   ctx tyA star
  strict d v_ctx b   tyB
  where
    v_ctx = pushVar rel v tyA ctx
typeCheck' d ctx ty (App b a rel) = do
  v <- newVar
  tyA <- newRef
  tyB <- newRef
  ty' <- ref (Pi rel v tyA tyB)
  subst d ctx v a tyA tyB ty
  strict d ctx a tyA
  strict d ctx b ty'
typeCheck' d ctx tyStar (CoPi c phi tyB) = do
  unifyD d ctx tyStar Star
  okPhi ctx phi
  strict d c_ctx tyB tyStar
  where
    c_ctx = pushCVar c phi ctx
typeCheck' d ctx ty (CoAbs c phi b) = do
  okPhi ctx phi
  tyB <- newRef
  unifyD d ctx ty (CoPi c phi tyB)
  strict d c_ctx b tyB
  where
    c_ctx = pushCVar c phi ctx
typeCheck' d ctx ty (CoApp a g) = do
  c <- newCVar
  phi <- newPhi
  tyB <- newRef
  ty' <- ref (CoPi c phi tyB)
  substC d ctx c g phi tyB ty
  strictC d ctx g phi
  strict d ctx a ty'

newPhi :: MonadGen m => m (EqProp (URef m a))
newPhi = liftA2 (:~:) newRef newRef

okPhi ctx (a :~: b) = unify emptyUnifyCtx a b  -- FIXME

ctxCheck v [] = False
ctxCheck v ((rel, v', _) : _) | v == v' = rel == Rel
ctxCheck v (_ : vs) = ctxCheck v vs

driver, codriver
  :: ( MonadGen m
     , Simple m p
     , Unifiable m (DCore_ p)
     )
  => D m p -> Ctx p -> DCore p -> DCore p -> m ()
driver d ctx tx ty = do
  tx' <- narrow ctx tx
  typeCheck d ctx tx' ty

codriver d ctx tx ty = do
  bindRef tx $ \ tx' ->
    typeCheck d ctx tx' ty

narrow
  :: ( MonadGen m
     , Simple m p
     )
  => Ctx p -> DCore p -> m (DCore_ p)
narrow ctx tx = do
  tx_ <- getRef tx
  case tx_ of
    Just tx' -> return tx'
    Nothing -> do
      tx' <- generateHead ctx
      setRef tx tx'
      return tx'

generateHead
  :: ( MonadGen m
     , Simple m p
     )
  => Ctx p -> m (DCore_ p)
generateHead ctx = choose
  [ 1 % g'Star
  , 1 % g'Var
  , 1 % g'Pi
  , 1 % g'Abs
  , 0 % g'App
  , 0 % g'Coerce
  , 0 % g'Fun
  , 0 % g'CoPi
  , 0 % g'CoAbs
  , 0 % g'CoApp
  ] >>= \g -> g ctx

g'Star, g'Var, g'Pi, g'Abs, g'App, g'Coerce, g'Fun, g'CoPi, g'CoAbs, g'CoApp
  :: ( MonadGen m
     , Simple m p
     )
  => Ctx p -> m (DCore_ p)
g'Star _ctx = return Star

g'Var ctx = selectVar (varCtx ctx)
  where
    selectVar [] = empty
    selectVar ((Rel, v, _) : vs) = return (Var v) <|> selectVar vs
    selectVar ((Irr, _, _) : vs) = selectVar vs

g'Pi _ctx = do
  v <- newVar
  rel <- choose [ 1 % Rel, 1 % Irr ]
  tyA <- newRef
  tyB <- newRef
  return (Pi rel v tyA tyB)

g'Abs _ctx = do
  v <- newVar
  rel <- choose [ 1 % Rel, 1 % Irr ]
  tyA <- newRef
  b <- newRef
  return (Abs rel v tyA b)

g'App _ctx = do
  rel <- choose [ 1 % Rel, 1 % Irr ]
  b <- newRef
  a <- newRef
  return (App b a rel)

g'Coerce = undefined
g'Fun = undefined
g'CoPi = undefined
g'CoAbs = undefined
g'CoApp = undefined

----

generate :: Generator m p
generate ctx tx ty = choose'
  [ 1 % gStar
  , 1 % gVar
  , 1 % gPi
  , 1 % gAbs
  , 1 % gApp
  , 1 % gCoerce
  , 1 % gFun
  , 1 % gCoPi
  , 1 % gCoAbs
  , 1 % gCoApp
  ] where
    choose' xs = choose xs >>= \g -> g ctx tx ty

unify0 :: Unifiable m a => a -> a -> m ()
unify0 = unify emptyUnifyCtx

(&=) :: Unifiable m a => URef m a -> a -> m ()
r &= a = do
  ma <- getRef r
  for_ ma $ \ a' -> unify0 a a'
  setRef r a

gStar :: Generator m p
gStar _ctx tx ty = do
  tx &= Star
  ty &= Star

gVar :: Generator m p
gVar ctx tx ty = do
  (v, ty') <- pickVar (varCtx ctx)
  tx &= Var v
  unify0 ty ty'
  where
    pickVar ((Irr, _, _) : xs) = pickVar xs
    pickVar ((Rel, v, ty') : xs) = join $ choose
      [ 1 % return (v, ty')
      , 1 % pickVar xs
      ]
    pickVar [] = empty

gPi :: Generator m p
gPi ctx tx ty = do
  rel <- choose [ 1 % Rel, 1 % Irr ]
  tyA <- newRef
  tyB <- newRef
  v <- newVar
  tx &= Pi rel v tyA tyB
  ty &= Star
  generate (pushVar rel v tyA ctx) tyB tStar
  -- generate ctx tyA tStar
  where
    tStar = ty

gAbs :: Generator m p
gAbs ctx tx ty = do
  rel <- choose [ 1 % Rel, 1 % Irr ]
  tyA <- newRef
  tyB <- newRef
  txBody <- newRef
  v <- newVar
  tx &= Abs rel v tyA txBody
  ty &= Pi  rel v tyA tyB
  generate (pushVar rel v tyA ctx) txBody tyB
  -- ref Star >>= \tStar -> generate ctx tyA tStar

gApp :: Generator m p
gApp ctx tx ty = do
  rel <- choose [ 1 % Rel, 1 % Irr ]
  tyA <- newRef
  txFun <- newRef
  txArg <- newRef
  v <- newVar
  tx &= App txFun txArg rel
  generate ctx txArg tyA
  tyB <- unsubst ctx txArg ty
  tyFun <- ref (Pi rel v tyA tyB)
  generate ctx txFun tyFun

-- Try to unify a with subterms of (what is going to be) B[a/x]
unsubst
  :: (MonadGen m)
  => Ctx p
  -> DCore p      -- ^ a
  -> DCore p      -- ^ B[a/x]
  -> m (DCore p)  -- ^ B
unsubst = undefined

gCoerce = undefined
gFun    = undefined
gCoPi   = undefined
gCoAbs  = undefined
gCoApp  = undefined
