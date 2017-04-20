{-# LANGUAGE TypeFamilies #-}

module Decor.Soup.Tree where

import Control.Applicative
import qualified Data.Map as Map
import Decor.Soup
import Decor.Soup.Simple
import Decor.Types

data Tree

type instance RelT Tree = Rel
type instance FunT Tree = Constant
type instance VarT Tree = DeBruijnV
type instance BindVarT Tree = ()
type instance CVarT Tree = DeBruijnC
type instance BindCVarT Tree = ()
type instance DCore Tree = DCore_ Tree
type instance Coercion Tree = CoercionId


treeSolution :: S1 -> Maybe (DCore Tree, DCore Tree)
treeSolution s = liftA2 (,) (treeDCore s t0) (treeDCore s ty0)

treeDCore :: S1 -> DCId -> Maybe (DCore Tree)
treeDCore s t = do
  h <- Map.lookup t ((eqns . constraints) s)
  case h of
    Star -> Just Star
    Fun f -> Just (Fun f)
    Var v -> Just (Var v)
    Pi rel () t1 t2 -> Pi rel () <$> treeDCore s t1 <*> treeDCore s t2
    Abs rel () t1 t2 -> Abs rel () <$> treeDCore s t1 <*> treeDCore s t2
    App b a rel -> App <$> treeDCore s b <*> treeDCore s a <*> pure rel

step :: DCore Tree -> Maybe (DCore Tree)
step Star = Nothing
step (Fun _) = Nothing
step (Var _) = Nothing
step (Pi _ _ _ _) = Nothing
step (Abs Irr () t a) = Abs Irr () t <$> step a
step (App b a rel) =
  case (b, step b) of
    (_, Just b) -> Just (App b a rel)
    (Abs rel' () _ b, Nothing) | rel == rel' -> Just (sub a b)
    _ -> Nothing

sub :: DCore Tree -> DCore Tree -> DCore Tree
sub = sub' (DeBruijnV 0)

sub' :: DeBruijnV -> DCore Tree -> DCore Tree -> DCore Tree
sub' n a b = case b of
  Star -> Star
  Fun f -> Fun f
  Var v | v == n -> shiftTerm n a
        | v < n -> Var v
        | otherwise -> Var (shift v (-1))
  Pi rel () t1 t2 -> Pi rel () (sub' n a t1) (sub' (shift n 1) a t2)
  Abs rel () t1 t2 -> Abs rel () (sub' n a t1) (sub' (shift n 1) a t2)
  App t1 t2 rel -> App (sub' n a t1) (sub' n a t2) rel

shiftTerm :: DeBruijnV -> DCore Tree -> DCore Tree
shiftTerm (DeBruijnV n) a = shiftTerm' n (DeBruijnV 0) a

shiftTerm' :: Shift -> DeBruijnV -> DCore Tree -> DCore Tree
shiftTerm' n m a = case a of
  Star -> Star
  Fun f -> Fun f
  Var v
    | v < m -> Var v
    | otherwise -> Var (shift v n)
  Pi rel () t1 t2 -> Pi rel () (shiftTerm' n m t1) (shiftTerm' n (shift m 1) t2)
  Abs rel () t1 t2 -> Abs rel () (shiftTerm' n m t1) (shiftTerm' n (shift m 1) t2)
  App t1 t2 rel -> App (shiftTerm' n m t1) (shiftTerm' n m t2) rel
