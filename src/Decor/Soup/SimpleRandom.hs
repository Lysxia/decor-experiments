{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Decor.Soup.SimpleRandom where

import Control.Concurrent
import Control.Exception (AsyncException(..))
import Control.Monad.Catch
import Control.Monad.Free
import Control.Monad.Random
import Control.Monad.Reader

import Decor.Soup.Simple

randomSearch
  :: (MonadCatch m, MonadRandom m, MonadLogS Log m)
  => Int -> m (Either (String, S1) S1)
randomSearch n = randomSearch' n initS1 ok fail treeH1
  where
    ok s = return (Right s)
    fail _ e s = return (Left (e, s))

randomSearch'
  :: (MonadCatch m, MonadRandom m, MonadLogS (Int, s) m)
  => Int
  -> s
  -> (s -> m r)
  -> (Int -> String -> s -> m r)
  -> Tree_ s
  -> m r
randomSearch' fuel s ok fail t = handle h $ case t of
  Pure s -> ok s
  Free f -> case f of
    Tag _ (Free (Tag s' _)) -> fail (fuel-1) "Potential occurs-fail" s'
    Tag s' t' -> logS (fuel, s') >> randomSearch' fuel s' ok fail t'
    Fail e -> fail (fuel-1) e s
    Pick x ys -> randomPick fuel x ys (length ys)
  where

    h UserInterrupt = fail 0 "KILL" s
    h e = throwM e

    randomPick fuel x _ 0 = fail (fuel - 1) (show x) s
    randomPick fuel x ys n = do
      w <- getRandomR (0, n - 1)
      let (ys0, (y, t') : ys1) = splitAt w ys
          fail' fuel e s =
            if fuel == 0 then
              fail 0 ("[" ++ x ++ ":" ++ show y ++ "]\n" ++ e) s
            else
              randomPick fuel x (ys0 ++ ys1) (n - 1)
      randomSearch' fuel s ok fail' t'

type Log = (Int, S1)

class MonadLogS s m where
  logS :: s -> m ()

instance MonadLogS Log LogS where
  logS s = LogS $ ReaderT $ \m -> tryTakeMVar m >> putMVar m s >> return ()

newtype LogS a = LogS (ReaderT (MVar Log) IO a)
  deriving (Functor, Applicative, Monad, MonadThrow, MonadCatch, MonadRandom)

runLogS :: MVar Log -> LogS a -> IO a
runLogS m (LogS r) = runReaderT r m
