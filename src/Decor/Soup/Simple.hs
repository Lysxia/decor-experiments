{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Decor.Soup.Simple where

import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Lens.Micro.Platform
import Data.Map (Map)
import qualified Data.Map as Map

import Decor.Types
import Decor.Soup

type Alias = DCore_ Soup

data H1 = H1
  { eqns :: Map DCId Alias
  , ks1 :: [K1]
  } deriving Show

data K1
  = K1Id DCId DCId Shift Shift           -- ^ @u = v^n_m@ shift all indices >= m by n
  | K1Sub DCId DCId DeBruijnV DCId       -- ^ @u = v[w^n/n]@ substitute
  | K1Type Ctx DCId DCId
  | K1Rel Rel DeBruijnV DCId
  | K1WF Ctx
  deriving (Eq, Show)

k1Eq :: DCId -> DCId -> K1
k1Eq u v = K1Id u v 0 0

ksH1 :: Lens' (S H1) [K1]
ksH1 = l @"ks" . l @"ks"

eqnsH1 :: Lens' (S H1) (Map DCId Alias)
eqnsH1 = l @"ks" . l @"eqns"

instance KStore H1 where
  initStore = H1 Map.empty []
  andK = andKH1
  reduce = reduceH1
  extractKType r = M $ do
    ks <- use ksH1
    (go, ks) <- (lift . lift)
      [ (r ctx t ty, ks)
      | (K1Type ctx t ty, ks) <- focus ks ]
    ksH1 .= ks
    unM go

andKH1 :: K -> M H1 ()
andKH1 (KEqDC t (RHSHead h)) = M $ do
  eqns <- use eqnsH1
  case Map.lookup t eqns of
    Nothing -> eqnsH1 %= Map.insert t h
    Just h' -> do
      ks <- eqHeadH1 h h'
      ksH1 %= (ks ++)

eqHeadH1 :: DCore_ Soup -> DCore_ Soup -> M' H1 [K1]
eqHeadH1 e1 e2 = case (e1, e2) of

  (Star, Star) -> return []
  (Star, _) -> empty

  (Var v1, Var v2) | v1 == v2 -> return []
  (Var{}, _) -> empty

  (Abs rel1 () tyA1 b1, Abs rel2 () tyA2 b2)
    | rel1 == rel2 ->
        [tyA1, b1] `eq` [tyA2, b2]
  (Abs{}, _) -> empty

  (Pi rel1 () tyA1 tyB1, Pi rel2 () tyA2 tyB2)
    | rel1 == rel2 ->
        [tyA1, tyB1] `eq` [tyA2, tyB2]
  (Pi{}, _) -> empty

  (App b1 a1 rel1, App b2 a2 rel2)
    | rel1 == rel2 ->
        [b1, a1] `eq` [b2, a2]
  (App{}, _) -> empty

  where
    eq a b = return $ zipWith k1Eq a b

reduceH1 :: M H1 ()
reduceH1 = M $ use ksH1 >>= reduceH1'

reduceH1' :: [K1] -> M' H1 ()
reduceH1' = loop
  where
    loop ks = do
      (ks', Any continue) <- runWriterT . fmap concat $ traverse reduceH1Atom ks
      if continue then
        loop ks'
      else
        ksH1 .= ks'

reduceH1Atom :: K1 -> WriterT Any (M' H1) [K1]
reduceH1Atom = undefined

{-

type RetryFlag = Bool

type CollectRetryCont a = [K] -> RetryFlag -> M' H1 a
type CollectRetry =
  forall a. CollectRetryCont a -> K -> M' H1 a

traverseCollectRetry
  :: CollectRetry
  -> [K]
  -> M' H1 [K]
traverseCollectRetry = traverseCollectRetry' []

traverseCollectRetry' :: [K] -> CollectRetry -> [K] -> M' H1 [K]
traverseCollectRetry' acc _collect [] = return acc
traverseCollectRetry' acc collect (k : ks) =
  (`collect` k) $ \moreKs retryFlag ->
    if retryFlag then
      traverseCollectRetry collect (moreKs ++ acc ++ ks)
    else
      traverseCollectRetry' (moreKs ++ acc) collect ks

reduceH1Atom :: CollectRetry
reduceH1Atom ret (KEqDC t (RHSId u shift)) = reduceH1EqDCId t u shift >> ret [] False
reduceH1Atom ret (KEqDC t (RHSHead f)) = reduceH1EqHead t f >> ret [] False
reduceH1Atom ret (KEqDC t (RHSSub tyA tyB)) =
  undefined -- reduceH1EqSub ret t x tyA tyB

reduceH1EqHead :: DCId -> DCore_ Soup -> M' H1 ()
reduceH1EqHead t f = do
  t_ <- lookupH1V t
  case t_ of
    Left t -> eqHead t f
    Right (_, e) -> reduceH1EqHeads' e f

reduceH1EqDCId :: DCId -> DCId -> M' H1 ()
reduceH1EqDCId t u = do
  t_ <- lookupH1V t
  u_ <- lookupH1V u
  case (t_, u_) of
    (Left t, Left u) | t == u -> return ()
    (Left t, Left u) -> alias t u
    (Left t, Right (_, f)) -> eqHead t f
    (Right (_, e), Left u) -> eqHead u e
    (Right (t, _), Right (u, _)) | t == u -> return ()
    (Right (_, e), Right (_, f)) ->
      reduceH1EqHeads' e f

eqHead :: DCId -> DCore_ Soup -> M' H1 ()
eqHead t e = do
  occursCheck' t e
  eqnsH1 %= Map.insert t (Head e)

occursCheck' :: DCId -> DCore_ Soup -> M' H1 ()
occursCheck' t e = case e of
  Star -> return ()
  Var _ -> return ()
  Abs _ _ tyA b -> mapM_ (occursCheck t) [tyA, b]
  Pi _ _ tyA tyB -> mapM_ (occursCheck t) [tyA, tyB]
  App b a _ -> mapM_ (occursCheck t) [b, a]

occursCheck :: DCId -> DCId -> M' H1 ()
occursCheck t u = do
  u_ <- lookupH1V u
  case u_ of
    Left u -> when (t == u) empty
    Right (u, f) -> do
      when (t == u) empty
      occursCheck' t f

alias :: DCId -> DCId -> M' H1 ()
alias t u = eqnsH1 %= Map.insert t (Alias u)

lookupH1V :: DCId -> M' H1 (Either DCId (DCId, DCore_ Soup))
lookupH1V t = do
  s <- get
  case Map.lookup t (s ^. eqnsH1) of
    Just (Alias v) -> lookupH1V v
    Nothing -> return (Left t)
    Just (Head e) -> return (Right (t, e))
-}

instance L "ks" H1 [K1] where
  l f h = fmap (\ks -> h { ks1 = ks }) (f (ks1 h))

instance L "eqns" H1 (Map DCId Alias) where
  l f h = fmap (\eqns -> h { eqns = eqns }) (f (eqns h))

