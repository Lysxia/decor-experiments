
module Decor.Soup.SimpleStreaming where

import Control.Monad
import Control.Monad.Free
import Control.Monad.Primitive
import Control.Monad.Random
import Data.Vector.Mutable (MVector)
import qualified Data.Vector.Mutable as MV

import Decor.Soup
import Decor.Soup.Simple

newtype Stream m s = Stream { unStream :: m (Maybe (s, Stream m s)) }

streamingSearch
  :: (WithParams, PrimMonad m, MonadRandom m)
  => Int -> Stream m S1
streamingSearch n = Stream $ do
  v <- MV.unsafeNew n
  MV.write v 0 treeH1
  streamingSearch' v 1

streamingSearch'
  :: (PrimMonad m, MonadRandom m)
  => MVector (PrimState m) (Tree_ s)
  -> Int
  -> m (Maybe (s, Stream m s))
streamingSearch' _ 0 = return Nothing
streamingSearch' v n = do
  i <- getRandomR (0, n-1)
  t <- MV.unsafeRead v i
  let clear k = do
        when (i < n - 1) $ MV.unsafeWrite v i =<< MV.unsafeRead v (n - 1)
        MV.unsafeWrite v (n - 1) undefined
        k (streamingSearch' v (n - 1))
  case t of
    Pure s -> clear (\continue -> return (Just (s, Stream continue)))
    Free f -> case f of
      Tag _ t -> do
        MV.unsafeWrite v i t
        streamingSearch' v n
      Pick _ xs@(_ : _) -> do
        t : ts <- shuffle (fmap snd xs)
        MV.unsafeWrite v i t
        n <- append v n ts
        streamingSearch' v n
      _ -> clear id

shuffle :: MonadRandom m => [a] -> m [a]
shuffle xs = shuffle' xs (length xs)
  where
    shuffle' _ 0 = return []
    shuffle' xs n = do
      i <- getRandomR (0, n-1)
      let (xs0, x : xs1) = splitAt i xs
      fmap (x :) (shuffle' (xs0 ++ xs1) (n - 1))

append :: PrimMonad m => MVector (PrimState m) a -> Int -> [a] -> m Int
append v n (a : as) | n < MV.length v = do
  MV.unsafeWrite v n a
  append v (n + 1) as
append _ n _ = return n
