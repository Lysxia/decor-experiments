{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Decor.Soup.SimpleRandom where

import Control.Concurrent
import Control.Exception (AsyncException(..))
import Control.Monad.Catch
import Control.Monad.Free
import Control.Monad.Random
import Control.Monad.Reader

import Decor.Soup
import Decor.Soup.Simple

data RandomSearchParams = RandomSearchParams
  { _maxFuel :: Int  -- Number of failures
  , _maxTries :: Int  -- Max branching factor
  , _maxDepth :: Int  -- Search depth
  , _varWeight :: Int  -- Increase probability of choosing a variable
  , _pickTypeOnce :: Bool
  }

type WithRandomSearchParams = (?randomSearchParams :: RandomSearchParams)

getFuel :: WithRandomSearchParams => Int
getFuel = _maxFuel ?randomSearchParams

maxTries :: WithRandomSearchParams => Int
maxTries = _maxTries ?randomSearchParams

maxDepth :: WithRandomSearchParams => Int
maxDepth = _maxDepth ?randomSearchParams

varWeight :: WithRandomSearchParams => Int
varWeight = _varWeight ?randomSearchParams

pickTypeOnce :: WithRandomSearchParams => Bool
pickTypeOnce = _pickTypeOnce ?randomSearchParams

randomSearch
  :: (WithParams, WithRandomSearchParams, MonadCatch m, MonadRandom m, MonadLogS Log m)
  => m (Either (String, S1) S1)
randomSearch = randomSearch' getFuel maxDepth initS1 ok fail treeH1
  where
    ok s = return (Right s)
    fail _ e s = return (Left (e, s))

randomSearch'
  :: forall m s r
  .  (MonadCatch m, MonadRandom m, MonadLogS (Int, s) m, WithRandomSearchParams)
  => Int
  -> Int
  -> s
  -> (s -> m r)
  -> (Int -> String -> s -> m r)
  -> Tree_ s
  -> m r
randomSearch' fuel depth s ok fail t = handle h $ case t of
  Pure s -> ok s
  _ | depth == 0 -> fail fuel "Max depth reached" s
  Free f -> case f of
    Tag _ (Free (Tag s' _)) -> fail (fuel-1) "Potential occurs-fail" s'
    Tag s' t' -> logS (fuel, s') >> randomSearch' fuel (depth-1) s' ok fail t'
    Fail e -> fail (fuel-1) e s
    Pick _ [(_, t')] -> randomSearch' fuel (depth-1) s ok fail t'
    Pick "Type" ys | pickTypeOnce -> do
      i <- getRandomR (0, length ys - 1)
      let (y, t') : _ = drop i ys
          fail' fuel e s = fail fuel ("{" ++ show y ++ "}\n" ++ e) s
      randomSearch' fuel (depth-1) s ok fail' t'
    Pick x ys ->
      let wys = [(weight t, (y, t)) | (y, t) <- ys]
      in randomPick maxTries fuel x wys ((sum . fmap fst) wys)
    Check t' -> randomSearch' fuel (depth-1) s ok fail t'
  where

    h ThreadKilled = fail 0 "KILL" s
    h UserInterrupt = fail 0 "INT" s
    h e = throwM e

    randomPick :: Show y => Int -> Int -> String -> [(Int, (y, Tree_ s))] -> Int -> m r
    randomPick triesLeft fuel x _ n | n == 0 || triesLeft == 0 = fail (fuel - 1) (show x) s
    randomPick triesLeft fuel x wys n = do
      w <- getRandomR (0, n - 1)
      go w [] wys $ \(w', (y, t')) wys' ->
        let
          fail' fuel e s =
            if fuel == 0 then
              fail 0 ("[" ++ x ++ ":" ++ show y ++ "]\n" ++ e) s
            else
              randomPick (triesLeft - 1) fuel x wys' (n - w')
        in randomSearch' fuel (depth-1) s ok fail' t'
    go w wys0 (wy@(w', _) : wys1) k
      | w < w' = k wy (wys0 ++ wys1)
      | otherwise = go (w - w') (wy : wys0) wys1 k
    go _ _ [] _ = error "assert false"

type Log = (Int, S1)

class MonadLogS s m where
  logS :: s -> m ()

instance MonadLogS Log LogS where
  logS s = LogS $ ReaderT $ \m -> tryTakeMVar m >> putMVar m s >> return ()

newtype LogS a = LogS (ReaderT (MVar Log) IO a)
  deriving (Functor, Applicative, Monad, MonadThrow, MonadCatch, MonadRandom)

runLogS :: MVar Log -> LogS a -> IO a
runLogS m (LogS r) = runReaderT r m

weight :: WithRandomSearchParams => Tree_ s -> Int
weight = weight' 3

weight' :: WithRandomSearchParams => Int -> Tree_ s -> Int
weight' _ (Free (Pick "Var" _)) = varWeight
weight' 0 _ = 1
weight' n (Free (Tag _ t)) = weight' (n-1) t
weight' _ _ = 1
