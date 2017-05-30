{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RecordWildCards #-}

module Decor.Soup.SimpleIO where

import Control.Concurrent
import Control.Exception
import Control.Monad
import Decor.Soup
import Decor.Soup.Simple
import Decor.Soup.SimpleRandom
import Decor.Soup.SimpleStreaming

data GenParams = GenParams
  { genSecs :: Int
  , subGenSecs :: Maybe Int
  }

generate
  :: (WithParams, WithRandomSearchParams)
  => GenParams -> IO (History, Either (String, S1) S1)
generate GenParams{..} = do
  m <- newEmptyMVar
  log <- newMVar []
  result <- newEmptyMVar
  tid <- forkIO $ mask $ \restore ->
    restore (runLogS m randomSearch) >>= putMVar result
  let loop 0 = killThread tid
      loop n = do
        threadDelay (10 ^ 6)
        x <- tryTakeMVar m
        modifyMVar_ log (return . (x :))
        loop (n - 1)
  tid2 <- forkIO $ loop genSecs
  s <- takeMVar result
  h <- readMVar log
  killThread tid2
  return (h, s)

generateS
  :: (WithParams, WithRandomSearchParams)
  => GenParams
  -> Int
  -> MVar S1
  -> IO ThreadId
generateS g@GenParams{..} width out = forkIO $
  forever $
    timeout genSecs $ runStream stream $ putMVar out
  where
    stream = streamingSearch evaluate' width
    evaluate' = case subGenSecs of
      Nothing -> return . Just
      Just secs -> timeout secs . evaluate

runStream :: Monad m => Stream m a -> (a -> m ()) -> m ()
runStream (Stream continue) k = do
  x <- continue
  case x of
    Nothing -> return ()
    Just (a, stream) -> k a >> runStream stream k

timeout :: Int -> IO a -> IO (Maybe a)
timeout secs t = do
  result <- newEmptyMVar
  tid <- forkIO $ Just <$> t >>= tryPutMVar result >> return ()
  forkIO $ threadDelay (secs * 10 ^ 6) >> killThread tid >> tryPutMVar result Nothing >> return ()
  takeMVar result
