{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TemplateHaskell #-}

module Decor.Tree.Lazy where

import Control.Search
import qualified Decor.Types as D
import Decor.Types.Convert
import Decor.Parser

data Term
  = Star
  | Var Integer
  | Pi Term Term
  | Lam Term Term
  | App Term Term Term

deriveEnumerable ''Term

termToTree :: Term -> D.DCore D.Tree
termToTree t = case t of
  Star -> D.Star
  Var i -> D.Var (D.DeBruijnV i)
  Pi a b -> D.Pi D.Rel () (termToTree a) (termToTree b)
  Lam a b -> D.Abs D.Rel () (termToTree a) (termToTree b)
  App a _ b -> D.App (termToTree a) (termToTree b) D.Rel

instance Show Term where
  show = show . ($ 0) . showDCore . convertTreeToPartial . termToTree

data CoolM a = CoolM Cool (Either String a)
  deriving Functor

instance Applicative CoolM where
  pure a = CoolM true (Right a)
  CoolM x f <*> CoolM y a = CoolM (x &&& y) (f <*> a)

instance Monad CoolM where
  CoolM x (Right a) >>= f =
    let CoolM y b = f a
    in CoolM (x &&& y) b
  CoolM x (Left e) >>= _ = CoolM x (Left e)
  fail e = CoolM false (Left e)

tellCool :: Cool -> CoolM ()
tellCool cool = CoolM cool (Right ())

anyway :: a -> CoolM () -> CoolM a
anyway a (CoolM x _) = CoolM x (Right a)

class CEq a where
  (===) :: a -> a -> Cool

instance CEq Term where
  Star === Star = true
  Var i === Var j | i == j = true
  Pi a b === Pi a' b' = a === a' &&& b === b'
  Lam a b === Lam a' b' = a === a' &&& b === b'
  App a b c === App a' b' c' = a === a' &&& b === b' &&& c === c'
  _ === _ = false

-- Lazy type checker
typeCheck :: Term -> Term -> Cool
typeCheck = typeCheck' []

typeCheck' :: [Term] -> Term -> Term -> Cool
typeCheck' ctx t ty = case t of
  Star -> ty === Star
  Var i
    | Just ty' <- lookupCtx i ctx -> ty === ty'
    | otherwise -> false
  Pi tyA tyB ->
    ty === Star
    &&& typeCheck' ctx tyA Star
    &&& typeCheck' (tyA : ctx) tyB Star
  Lam tyA b ->
    case ty of
      Pi tyA' tyB' ->
        typeCheck' (tyA' : ctx) b tyB'
        &&& tyA === tyA'
        &&& typeCheck' ctx tyA' Star
      _ -> false
  App b tyB a ->
    case tyB of
      Pi tyA' tyB' ->
        typeCheck' ctx a tyA'
        &&& typeCheck' ctx b tyB
        &&& ty === sub a tyB'
      _ -> false

notStar :: Term -> Cool
notStar t = case t of
  Star -> false
  Pi _ t' -> notStar t'
  _ -> true

sub :: Term -> Term -> Term
sub = sub' 0

sub' :: Integer -> Term -> Term -> Term
sub' i0 s t = case t of
  Star -> Star
  Var i
    | i == i0 -> shiftTerm i0 s
    | i < i0 -> Var i
    | otherwise -> Var (i - 1)
  Pi tyA tyB -> Pi (sub' i0 s tyA) (sub' (i0 + 1) s tyB)
  Lam tyA b -> Lam (sub' i0 s tyA) (sub' (i0 + 1) s b)
  App b tyB a -> App (sub' i0 s b) (sub' i0 s tyB) (sub' i0 s a)

shiftTerm :: Integer -> Term -> Term
shiftTerm = shiftTerm' 0

shiftTerm' :: Integer -> Integer -> Term -> Term
shiftTerm' k i0 t = case t of
  Star -> Star
  Var i
    | i < k -> Var i
    | otherwise -> Var (i + i0)
  Pi tyA tyB -> Pi (shiftTerm' k i0 tyA) (shiftTerm' (k + 1) i0 tyB)
  Lam tyA b -> Lam (shiftTerm' k i0 tyA) (shiftTerm' (k + 1) i0 b)
  App b tyB a -> App (shiftTerm' k i0 b) (shiftTerm' k i0 tyB) (shiftTerm' k i0 a)

lookupCtx :: Integer -> [Term] -> Maybe Term
lookupCtx i _ | i < 0 = Nothing
lookupCtx i ctx =
  let n = fromIntegral i
  in case drop n ctx of
    [] -> Nothing
    t : _ -> Just (shiftTerm (i + 1) t)
