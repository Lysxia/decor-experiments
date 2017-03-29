{-# LANGUAGE FlexibleInstances #-}

module Decor.Soup.Trivial where

import Control.Comonad.Cofree
import Control.Monad.State.Strict
import Decor.Soup

type HTrivial = [K]

instance KStore [K] where
  initStore = []
  andK k = M . modify' $ \s -> s {constraints = k : constraints s}
  reduce = return ()
  extractKType r = M $ do
    s <- get
    case break isKType (constraints s) of
      (cs, KType ctx t ty : cs') -> do
        put (s { constraints = cs ++ cs' })
        unM (r ctx t ty)
      _ -> (lift . lift) []

tree' :: Cofree (Elide ForkF) (S HTrivial)
tree' = takeDepth 2 tree
