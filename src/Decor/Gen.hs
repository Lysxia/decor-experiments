-- | Random generation, with narrowing and backtracking.

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}

module Decor.Gen where

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans.Class
import Data.STRef
import QuickCheck.GenT hiding (MonadGen)

class (Monad m, Alternative m) => MonadGen m where
  data URef m :: * -> *  -- Unifiable reference
  newInteger :: m Integer
  newRef :: m (URef m a)
  getRef :: URef m a -> m (Maybe a)
  setRef :: URef m a -> a -> m ()
  mergeRef :: URef m a -> URef m a -> m ()
  bindRef :: URef m a -> (a -> m ()) -> m ()
  choose :: [(Int, a)] -> m a

ref :: MonadGen m => a -> m (URef m a)
ref a = newRef >>= \r -> setRef r a *> return r

type G s a = GenT (ST s) a

data S = S
  { fuel :: !Int
  , counter :: !Integer
  }

newtype Gen r s a = Gen
  { unGen
      :: (a -> (S -> G s r) -> S -> G s r)
      -> (S -> G s r)
      -> S
      -> G s r
  }

liftG :: G s a -> Gen r s a
liftG ma = Gen $ \ k fail s ->
  ma >>= \ a -> k a fail s

liftGST :: ST s a -> Gen r s a
liftGST = liftG . lift

instance Functor (Gen r s) where
  fmap = liftA

instance Applicative (Gen r s) where
  pure a = Gen $ \ k -> k a
  (<*>) = ap

instance Monad (Gen r s) where
  ma >>= f = Gen $ \ k fail s ->
    unGen ma
      (\ a fail s -> unGen (f a) k fail s)
      fail s

instance Alternative (Gen r s) where
  empty = Gen $ \ _ fail -> fail
  ma <|> ma' = Gen $ \ k fail s ->
    let
      fail' s | fuel s == 0 = fail s
      fail' s = unGen ma' k fail $! s{ fuel = fuel s - 1 }
    in
      unGen ma k fail' s

data Unknown r s a
  = Unknown (a -> Gen r s ())
  | Known a

maybeUnk :: Unknown r s a -> Maybe a
maybeUnk (Known a) = Just a
maybeUnk (Unknown _) = Nothing

instance MonadGen (Gen r s) where
  newtype URef (Gen r s) a = GenURef (STRef s (Unknown r s a))

  newInteger = Gen $ \ k fail s ->
    let
      i = counter s
      !s' = s { counter = i + 1 }
    in
      k i fail s'

  newRef = liftGST (GenURef <$> newSTRef (Unknown (\ _ -> return ())))

  getRef (GenURef r) = liftGST (maybeUnk <$> readSTRef r)

  setRef (GenURef r) a = do
    a_ <- liftGST (readSTRef r)
    case a_ of Unknown k -> k a ; Known _ -> return ()
    liftGST (writeSTRef r (Known a))
