-- | Random generation, with narrowing and backtracking.

{-# LANGUAGE TypeFamilies #-}

module Decor.Gen where

import Control.Applicative

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

