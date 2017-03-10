{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module DCore where

import Control.Applicative
import Control.Monad
import Data.Foldable

import GHC.Generics
import Generics.OneLiner

import qualified Data.Map as Map
import qualified Data.Sequence as Seq

type family VarT  p
type family BindVarT p
type family FunT  p
type family CVarT p
type family BindCVarT p
type family RelT p
type family DCore p
type family Coercion p

-- | Relevance
data Rel = Rel | Irr
  deriving (Eq, Show)

data DCore_ p

  = Star
  | Var (VarT p)
  | Fun (FunT p)

  | Abs (RelT p) (BindVarT p) (DCore p) (DCore p)
  | Pi (RelT p) (BindVarT p) (DCore p) (DCore p)
  | App (DCore p) (DCore p) (RelT p)

  | CoAbs (BindCVarT p) (EqProp (DCore p)) (DCore p)
  | CoPi (BindCVarT p) (EqProp (DCore p)) (DCore p)
  | CoApp (DCore p) (Coercion p)

  | Coerce (DCore p) (Coercion p)

  deriving Generic

deriving instance
  ( Show (VarT p)
  , Show (FunT p)
  , Show (RelT p)
  , Show (BindVarT p)
  , Show (BindCVarT p)
  , Show (CVarT p)
  , Show (DCore p)
  , Show (Coercion p)
  ) => Show (DCore_ p)

data Coercion_ p
  = CVar (CVarT p)
  | CRefl (DCore p)
  | CRefl' (DCore p) (DCore p) (Coercion p)
  | CSym (Coercion p)
  | CSeq (Coercion p) (Coercion p)
  | CRed (DCore p) (DCore p)
  | CAbs (RelT p) (BindVarT p) (Coercion p) (Coercion p)
  | CApp (Coercion p) (Coercion p) Rel
  | CPi (RelT p) (BindVarT p) (Coercion p) (Coercion p)
  | CCoAbs (BindCVarT p) (Coercion p) (Coercion p) (Coercion p)
  | CCoPi (BindCVarT p) (Coercion p) (Coercion p)
  | CCoApp (Coercion p) (Coercion p) (Coercion p)
  deriving Generic

deriving instance
  ( Show (VarT p), Show (FunT p), Show (RelT p), Show (BindVarT p)
  , Show (DCore p)
  , Show (BindCVarT p)
  , Show (CVarT p)
  , Show (Coercion p)
  ) => Show (Coercion_ p)

data EqProp a = (:~:) a a
  deriving (Eq, Show)

data Partial (f :: *) (r :: * -> *)

newtype DeBruijn = DeBruijn Integer
  deriving (Eq, Show, Num)

newtype FunId = FunId Integer
  deriving (Eq, Ord, Show)

type instance VarT      (Partial f r) = DeBruijn
type instance BindVarT  (Partial f r) = ()
type instance FunT      (Partial f r) = f
type instance CVarT     (Partial f r) = DeBruijn
type instance BindCVarT (Partial f r) = ()
type instance RelT      (Partial f r) = Rel
type instance DCore     (Partial f r) = r (DCore_ (Partial f r))
type instance Coercion  (Partial f r)
  = TODO
  -- = r (Coercion_ (Partial f r))

data TODO = TODO
  deriving (Eq, Show)

class (Monad m, Alternative m) => MonadGen m where
  data URef m :: * -> *  -- Unifiable reference
  newRef :: m (URef m a)
  getRef :: URef m a -> m (Maybe a)
  setRef :: URef m a -> a -> m ()
  mergeRef :: URef m a -> URef m a -> m ()
  choose :: [(Int, a)] -> m a
  continue :: [(Int, m ())] -> m ()
  redundant :: [m ()] -> m ()
  final :: [m ()] -> m ()

ref :: MonadGen m => a -> m (URef m a)
ref a = newRef >>= \r -> setRef r a *> return r

class MonadGen m => Unifiable m a where
  unify :: a -> a -> m ()

instance Unifiable m a => Unifiable m (URef m a) where
  unify r s = do
    ma <- getRef r
    mb <- getRef s
    for_ ma $ \ a ->
      for_ mb $ \ b ->
        unify a b
    mergeRef r s

instance {-# OVERLAPPABLE #-} (MonadGen m, Eq a) => Unifiable m a where
  unify a a'
    | a == a' = return ()
    | otherwise = empty

instance
  ( MonadGen m
  , UnifiableFields m p
  ) => Unifiable m (DCore_ p) where
  unify t t' = unAM
    (mzipWith
      (For :: For (Unifiable m))
      (\i j -> AM (unify i j))
      t
      t')

instance Unifiable m a => Unifiable m (EqProp a) where
  unify (a :~: b) (a' :~: b') = unify a a' *> unify b b'

newtype AM m = AM { unAM :: m () }

instance Applicative m => Monoid (AM m) where
  mempty = AM (pure ())
  mappend (AM a) (AM b) = AM (a *> b)

type UnifiableFields m p =
  ( Unifiable m (VarT p)
  , Unifiable m (BindVarT p)
  , Unifiable m (FunT p)
  , Unifiable m (RelT p)
  , Unifiable m (DCore p)
  , Unifiable m (CVarT p)
  , Unifiable m (BindCVarT p)
  , Unifiable m (Coercion p)
  )

(%) :: a -> b -> (a, b)
(%) = (,)

data Ctx p = Ctx
  { refCtx :: RecCtx p
  , varCtx :: VarCtx p
  , cVarCtx :: CVarCtx p
  }

type RecCtx p = Map.Map (FunT p) (DCore p)
type VarCtx p = [(Rel, DCore p)]
type CVarCtx p = Seq.Seq (EqProp (DCore p))

pushVar :: Rel -> DCore p -> Ctx p -> Ctx p
pushVar rel ty ctx = ctx { varCtx = (rel, ty) : varCtx ctx }

type Generator m p
  =  ( MonadGen m
     , DCore p ~ URef m (DCore_ p)
     , VarT p ~ DeBruijn
     , BindVarT p ~ ()
     , RelT p ~ Rel
     , Unifiable m (DCore_ p)
     )
  => Ctx p
  -> DCore p  -- ^ Term
  -> DCore p  -- ^ Type
  -> m ()

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

(&=) :: Unifiable m a => URef m a -> a -> m ()
r &= a = do
  ma <- getRef r
  for_ ma $ \ a' -> unify a a'
  setRef r a

gStar :: Generator m p
gStar ctx tx ty = do
  tx &= Star
  ty &= Star

gVar :: Generator m p
gVar ctx tx ty = do
  (v, ty') <- pickVar 0 (varCtx ctx)
  tx &= Var v
  unify ty ty'
  where
    pickVar n ((Irr, _) : xs) = pickVar (n + 1) xs
    pickVar n ((Rel, ty') : xs) = join $ choose
      [ 1 % return (n, ty')
      , 1 % pickVar (n + 1) xs
      ]

gPi :: Generator m p
gPi ctx tx ty = do
  rel <- choose [ 1 % Rel, 1 % Irr ]
  tyA <- newRef
  tyB <- newRef
  tx &= Pi rel () tyA tyB
  ty &= Star
  generate (pushVar rel tyA ctx) tyB tStar
  -- generate ctx tyA tStar
  where
    tStar = ty

gAbs :: Generator m p
gAbs ctx tx ty = do
  rel <- choose [ 1 % Rel, 1 % Irr ]
  tyA <- newRef
  tyB <- newRef
  txBody <- newRef
  tx &= Abs rel () tyA txBody
  ty &= Pi  rel () tyA tyB
  generate (pushVar rel tyA ctx) txBody tyB
  -- ref Star >>= \tStar -> generate ctx tyA tStar

gApp :: Generator m p
gApp ctx tx ty = do
  rel <- choose [ 1 % Rel, 1 % Irr ]
  tyFun <- newRef
  tyA <- newRef
  txFun <- newRef
  txArg <- newRef
  tx &= App txFun txArg rel
  generate ctx txArg tyA
  tyB <- unsubst ctx txArg ty
  tyFun <- ref (Pi rel () tyA tyB)
  generate ctx txFun tyFun

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
