
module Decor.Soup.SimpleStreaming where

import Control.Applicative
import Control.Monad
import Control.Monad.Free
import Control.Monad.Primitive
import Control.Monad.Random
import Control.Monad.Ref
import Data.Foldable (for_)
import Data.Vector.Mutable (MVector)
import qualified Data.Vector.Mutable as MV

import Decor.Soup
import Decor.Soup.Simple
import Decor.Soup.SimpleRandom

newtype Stream m s = Stream { unStream :: m (Maybe (s, Stream m s)) }

streamingSearch
  :: (WithParams, WithRandomSearchParams, PrimMonad m, MonadRandom m, MonadRef r m)
  => (Tree_ S1 -> m (Maybe (Tree_ S1))) -> Int -> Stream m S1
streamingSearch evaluate n = Stream $ do
  v <- MV.unsafeNew n
  MV.write v 0 (treeH1, maxDepth, Nothing)
  streamingSearch' evaluate v 1

streamingSearch'
  :: (PrimMonad m, MonadRandom m, MonadRef r m, WithRandomSearchParams)
  => (Tree_ s -> m (Maybe (Tree_ s)))
  -> MVector (PrimState m) (Tree_ s, Int, Maybe (r Bool))
  -> Int
  -> m (Maybe (s, Stream m s))
streamingSearch' _ _ 0 = return Nothing
streamingSearch' evaluate v n = do
  i <- getRandomR (0, n-1)
  (t, d, m) <- MV.unsafeRead v i
  let clear k = do
        when (i < n - 1) $ MV.unsafeWrite v i =<< MV.unsafeRead v (n - 1)
        MV.unsafeWrite v (n - 1) undefined
        k (streamingSearch' evaluate v (n - 1))
  late <- case m of
    Just r -> readRef r
    Nothing -> return False
  t'@ ~(Just t) <-
    if d == 0 || late then
      return Nothing
    else
      evaluate t
  case t of
    _ | Nothing <- t' -> clear id
    Pure s -> do
      for_ m $ \r -> writeRef r True
      clear (\continue -> return (Just (s, Stream continue)))
    Free f -> case f of
      Tag _ t -> do
        MV.unsafeWrite v i (t, d-1, m)
        streamingSearch' evaluate v n
      Pick "Type" ts | pickTypeOnce -> do
        i <- getRandomR (0, length ts - 1)
        let (_, t) : _ = drop i ts
        MV.unsafeWrite v i (t, d-1, m)
        streamingSearch' evaluate v n
      Pick _ xs@(_ : _) -> do
        tdm : ts <- shuffle maxTries [(weight t, (t, d-1, m)) | (_, t) <- xs]
        MV.unsafeWrite v i tdm
        n <- append v n ts
        streamingSearch' evaluate v n
      Check t -> do
        r <- newRef False
        MV.unsafeWrite v i (t, d-1, m <|> Just r)
        streamingSearch' evaluate v n
      Fail _ -> clear id
      Pick _ [] -> clear id

shuffle :: MonadRandom m => Int -> [(Int, a)] -> m [a]
shuffle k xs = shuffle' k xs ((sum . fmap fst) xs)
  where
    shuffle' k _ n | k == 0 || n == 0 = return []
    shuffle' k as n = do
      i <- getRandomR (0, n-1)
      go i [] as $ \j' a as' ->
        fmap (a :) (shuffle' (k-1) as' (n - j'))
    go i as0 ((j, a) : as1) kont
      | i < j = kont j a (as0 ++ as1)
      | otherwise = go (i - j) ((j, a) : as0) as1 kont
    go _ _ [] _ = error "assert false"

append :: PrimMonad m => MVector (PrimState m) a -> Int -> [a] -> m Int
append v n (a : as) | n < MV.length v = do
  MV.unsafeWrite v n a
  append v (n + 1) as
append _ n _ = return n
