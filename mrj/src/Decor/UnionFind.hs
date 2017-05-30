module Decor.UnionFind where

import Data.Map (Map)
import qualified Data.Map as Map

newtype UnionFind a = UnionFind { unUF :: Map a (Either Int a) }
  deriving Show

emptyUF :: UnionFind a
emptyUF = UnionFind Map.empty

rootUF :: Ord a => a -> UnionFind a -> a
rootUF a uf = rootUF' a uf $ \a' _ _ -> a'

rootUF'
  :: Ord a
  => a -> UnionFind a -> (a -> Int -> (a -> UnionFind a -> UnionFind a) -> r) -> r
rootUF' a uf k =
  case Map.lookup a (unUF uf) of
    Nothing -> k a 1 h
    Just (Left n) -> k a n h
    Just (Right a') -> rootUF' a' uf $ \a0 n0 k0 -> k a0 n0 $ \a' -> k0 a' . h a'
  where
    h a' = UnionFind . Map.insert a (Right a') . unUF

mergeUF :: Ord a => a -> a -> UnionFind a -> UnionFind a
mergeUF a b = snd . mergeUF' a b

mergeUF' :: Ord a => a -> a -> UnionFind a -> (a, UnionFind a)
mergeUF' a b uf =
  rootUF' a uf $ \a' n updateA ->
    rootUF' b uf $ \b' m updateB ->
      let
        merge c =
          (,) c . UnionFind . Map.insert c (Left (n + m)) . unUF . updateA c . updateB c
      in
        merge (if n > m then a' else b') uf

equalUF :: Ord a => a -> a -> UnionFind a -> Bool
equalUF a b uf =
  rootUF' a uf $ \a _ _ -> rootUF' b uf $ \b _ _ ->
    a == b

