{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

import Brick
import Graphics.Vty (Key(..), Event(..), Modifier(..), defAttr)

import Control.Concurrent
import Control.Exception
import Control.Monad
import Control.Monad.Free
import Data.Either
import Data.Foldable
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (fromMaybe)
import Options.Generic
import System.Environment (getArgs)
import System.IO
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as Map

import Decor.Soup
import Decor.Soup.Simple
import Decor.Soup.SimpleRandom
import Decor.Soup.SimpleStreaming

data Options
  = Gen
  { _out :: Maybe String
  , _secs :: Maybe Int
  , _fuel :: Maybe Int
  }
  | Streaming
  { _out :: Maybe String
  , _secs :: Maybe Int
  , _width :: Maybe Int
  , _iter :: Maybe Int
  }
  | RunApp
  { _out :: Maybe String
  } deriving Generic

_file :: Options -> String
_file = fromMaybe "decor-log" . _out

instance ParseRecord Options where
  parseRecord = parseRecordWithModifiers defaultModifiers{fieldNameModifier=tail}

main = do
  opts <- getRecord "decor"
  case opts of
    Gen{} -> search opts
    RunApp{} -> runApp opts
    Streaming{} -> stream opts

stream :: Options -> IO ()
stream opts = do
  let width = fromMaybe 100 (_width opts)
      stream = streamingSearch width
      streamWith' = streamWith (_iter opts) stream
      runStream = case _out opts of
        Nothing -> streamWith' stdout
        Just file -> withFile file WriteMode streamWith'
  m <- newEmptyMVar
  tid <- forkFinally runStream $ \_ -> putMVar m ()
  case _secs opts of
    Nothing -> do
      () <- takeMVar m
      return ()
    Just secs -> do
      threadDelay (secs * 10^6)
      killThread tid

streamWith :: Maybe Int -> Stream IO S1 -> Handle -> IO ()
streamWith (Just 0) _ _ = return ()
streamWith n (Stream continue) h = do
  x <- continue
  case x of
    Nothing -> return ()
    Just (s, continue) -> do
      hPutStrLn h (showSolution s)
      streamWith (fmap (subtract 1) n) continue h

search :: Options -> IO ()
search opts = do
  let fuel = fromMaybe 100 (_fuel opts)
  m <- newEmptyMVar
  log <- newMVar []
  result <- newEmptyMVar
  tid <- forkIO $ mask $ \restore ->
    restore (runLogS m (randomSearch fuel)) >>= putMVar result
  let loop 0 = killThread tid
      loop n = do
        threadDelay (10 ^ 6)
        x <- tryTakeMVar m
        modifyMVar_ log (return . (x :))
        loop (n - 1)
  tid2 <- forkIO $ loop (fromMaybe 10 (_secs opts))
  let history = do
        xs <- readMVar log
        return $ do
          Just (fuel, s) <- xs
          [replicate 30 '=', show fuel, showCurrentDerivation s]
  let h BlockedIndefinitelyOnMVar =
        for_ (_out opts) $ \file -> do
          writeFile file . unlines =<< history
          putStrLn $ "Search sample written to " ++ file
  handle h $ do
    s <- takeMVar result
    xs <- readMVar log
    killThread tid2
    case s of
      Right s -> do
        putStrLn "SUCCESS\n"
        putStrLn (showSolution s)
        for_ (_out opts) $ \file -> do
          writeFile file $ showCurrentDerivation s
          putStrLn $ "Derivation written to " ++ file
      Left (e, s) ->
        for_ (_out opts) $ \file -> do
          history <- history
          writeFile file . unlines $
            [ "FAIL"
            , e
            , showCurrentDerivation s
            ] ++ history
          putStrLn $ "Search state written to " ++ file

runApp :: Options -> IO ()
runApp opts = do
  ((zs, k) :| _) <- defaultMain
    app
    (return (children initS1 treeH1, 0))
  case _out opts of
    Nothing -> return ()
    Just file ->
      level zs k (return ()) $ \_ s _ -> do
        writeFile file . unlines $
          [ showSolution s
          , showCurrentDerivation s
          ]
        putStrLn $ "Derivation written to " ++ file

type Zs = [(String, S1, Tree_ S1)]

main_window = "main"
e_window = "e"
k_window = "k"

level :: Zs -> Int -> r -> (String -> S1 -> Tree_ S1 -> r) -> r
level zs k r cont = case drop k zs of
  (key, s, t) : _ -> cont key s t
  _ -> r

app :: App (NonEmpty (Zs, Int)) () String
app = App
  { appDraw = \history@((zs, k) :| _) ->
      level zs k [str "[]"] $ \key s t ->
        [ viewport main_window Both
            ( str . unlines $
                [ showSolution s
                , showCurrentDerivation s
                ])
          <+>
          ( str (showRoot t)
            <=>
            foldr
              ((<=>) . \(zs, k) ->
                level zs k (str "?") $ \key _ _ ->
                  str (show k ++ ". " ++ key))
              emptyWidget
              history
          )
          <=>
          ( vLimit 5 $
              ( viewport e_window Both .
                str . unlines . fmap show . Map.toList . eqns . constraints
              ) s
              <+>
              ( viewport k_window Both .
                str . unlines . fmap show . ks1 . constraints
              ) s
          )
        ]
  , appChooseCursor = \_ _ -> Nothing
  , appHandleEvent = \hs_@((zs, k) :| hs) e -> case e of
      VtyEvent e -> case e of
        EvKey (KChar 'h') [] -> hScrollBy scr (-1) >> continue hs_
        EvKey (KChar 'j') [] -> vScrollBy scr 1 >> continue hs_
        EvKey (KChar 'k') [] -> vScrollBy scr (-1) >> continue hs_
        EvKey (KChar 'l') [] -> hScrollBy scr 1 >> continue hs_

        EvKey (KChar 'y') [] -> hScrollBy scrK (-1) >> continue hs_
        EvKey (KChar 'u') [] -> vScrollBy scrK 1 >> continue hs_
        EvKey (KChar 'i') [] -> vScrollBy scrK (-1) >> continue hs_
        EvKey (KChar 'o') [] -> hScrollBy scrK 1 >> continue hs_

        EvKey (KChar 'Y') [] -> hScrollBy scrE (-1) >> continue hs_
        EvKey (KChar 'U') [] -> vScrollBy scrE 1 >> continue hs_
        EvKey (KChar 'I') [] -> vScrollBy scrE (-1) >> continue hs_
        EvKey (KChar 'O') [] -> hScrollBy scrE 1 >> continue hs_

        EvKey KUp   []
          | Just hs' <- NonEmpty.nonEmpty hs ->
              continue hs'
        EvKey KDown []
          | (_, s, t) : _ <- drop k zs, zs@(_ : _) <- children s t ->
              continue (NonEmpty.cons (zs, 0) hs_)
        EvKey KLeft  []
          | k > 0 ->
              continue ((zs, k - 1) :| hs)
        EvKey KRight []
          | k < length zs - 1 ->
              continue ((zs, k + 1) :| hs)
        EvKey (KChar 'q') [] -> halt hs_
        _ -> continue hs_
       where
         scr = viewportScroll main_window
         scrK = viewportScroll k_window
         scrE = viewportScroll e_window
      _ -> continue hs_
  , appStartEvent = return
  , appAttrMap = const (attrMap defAttr [])
  }

stateOf :: Tree_ s -> Maybe s
stateOf (Free (Tag s _)) = Just s
stateOf (Pure s) = Just s
stateOf _ = Nothing

children :: s -> Tree_ s -> [(String, s, Tree_ s)]
children _ (Pure s) = []
children s (Free f) = case f of
  Tag _ f@(Free (Tag _ _)) -> [name "Continue" f]
  Tag _ f -> children s f
  Pick d xfs -> [name ("Pick[" ++ d ++ "]" ++ ": " ++ show x) f | (x, f) <- xfs]
  Fail e -> []
  where
    name n t = (n, fromMaybe s (stateOf t), t)
