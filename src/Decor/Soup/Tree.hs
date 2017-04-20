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
