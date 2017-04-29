{-# LANGUAGE TypeFamilies #-}

module Decor.Tree where

import Control.Applicative
import Data.List (findIndex)
import qualified Data.Map as Map
import Text.Read (readMaybe)

import qualified Decor.Parser as P
import Decor.Soup
import Decor.Soup.Simple
import Decor.Types

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
-- step (Fun Zero) = Just (Abs Rel () (Fun Nat) (Fun Zero))
step (Fun _) = Nothing
step (Var _) = Nothing
step (Pi _ _ _ _) = Nothing
step (Abs Irr () t a) = Abs Irr () t <$> step a
step (Abs Rel _ _ _) = Nothing
step (App b a rel) =
  case (b, step b) of
    (_, Just b) -> Just (App b a rel)
    (Abs rel' () _ b, Nothing) | rel == rel' -> Just (sub a b)
    (App (App (App (Fun FoldNat) r relr) z relz) s rels, Nothing)
      | Fun Zero <- a -> Just z
      | App (Fun Succ) a _ <- a ->
          Just $ App (App (App (App (Fun FoldNat) r relr) (App s z Rel) relz) s rels) a rel
      | Just a <- step a ->
          Just $ App (App (App (App (Fun FoldNat) r relr) z relz) s rels) a rel
      | otherwise -> Nothing
    _ -> Nothing

preservation :: DCore Tree -> Bool
preservation t = case step t of
    Just t' -> typeOf t == typeOf t'
    Nothing -> True

progress :: DCore Tree -> Bool
progress t = case step t of
  Nothing -> isValue t
  Just _ -> True

strongProgress :: DCore Tree -> Bool
strongProgress t = case step t of
  Just t -> strongProgress t
  Nothing -> isValue t

isValue :: DCore Tree -> Bool
isValue (Fun _) = True
isValue (App (Fun Succ) _ _) = True
isValue (App (Fun FoldNat) _ _) = True
isValue (App (App (Fun FoldNat) _ _) _ _) = True
isValue (App (App (App (Fun FoldNat) _ _) _ _) _ _) = True
isValue (App _ _ _) = False
isValue _ = True

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

{-
compileCPS :: DCore Tree -> DCore Tree
compileCPS t = mkCPS t

mkCPS :: DCore Tree -> DCore Tree
mkCPS t =
  Abs Rel ()
    Star
    (Abs Rel ()
      (Pi Rel ()
        (shiftTerm (DeBruijnV 1) (typeOf t))
        (Var (DeBruijnV 1)))
      (App (Var (DeBruijnV 0)) (shiftTerm (DeBruijnV 2) t) Rel))
-}

typeOf :: DCore Tree -> Maybe (DCore Tree)
typeOf = typeOf' []

typeOf' _ Star = Just Star
typeOf' _ (Pi _ _ _ _) = Just Star
typeOf' _ (Fun f) = Just $ case f of
  Nat -> Star
  Zero -> Fun Nat
  Succ -> Pi Rel () (Fun Nat) (Fun Nat)
  FoldNat ->
    Pi Rel ()
      Star
      (Pi Rel ()
        (Var (DeBruijnV 0))
        (Pi Rel ()
          (Pi Rel () (Var (DeBruijnV 1)) (Var (DeBruijnV 2)))
          (Pi Rel () (Fun Nat) (Var (DeBruijnV 3)))))
typeOf' ctx (Var v@(DeBruijnV n)) = case drop (fromIntegral n) ctx of
  t : _ -> Just (shiftTerm (shift v 1) t)
  [] -> Nothing
typeOf' ctx (Abs rel () a b) = Pi rel () a <$> typeOf' (a : ctx) b
typeOf' ctx (App b a rel) = case typeOf' ctx b of
  Just (Pi rel' () tyB tyC) -> Just $ sub a tyC
  Nothing -> Nothing

unPartial :: DCoreP -> Maybe (DCore Tree)
unPartial = unPartial_ []

unPartial_ :: [String] -> DCoreP -> Maybe (DCore Tree)
unPartial_ ctx (Just t) = unPartial' [] t
unPartial_ _ Nothing = Nothing

unPartial' :: [String] -> DCore_ Partial -> Maybe (DCore Tree)
unPartial' ctx (Var v) = Var <$> DeBruijnV <$> fromIntegral <$> findIndex (== v) ctx
unPartial' ctx (Fun f) = Fun <$> readMaybe f
