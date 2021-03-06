{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

import Brick
import Graphics.Vty (Key(..), Event(..), Modifier(..), defAttr)

import Control.Concurrent
import Control.Exception
import Control.Monad
import Control.Monad.Free
import Data.Foldable
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (fromMaybe)
import Data.Traversable
import Options.Generic
import System.IO
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as Map

import qualified Decor.Parser as P
import Decor.Soup
import Decor.Soup.Simple
import Decor.Soup.SimpleRandom
import Decor.Soup.SimpleStreaming
import Decor.Soup.Tree

data RunMode = Gen | Streaming | RunApp | Retry deriving (Generic, Read, Show)

data Options_ w = Options
  { _mode :: w ::: RunMode <?> "RunApp;Gen;Streaming"
  , _out :: w ::: Maybe String <?> "Output file"
  , _eout :: w ::: Maybe String <?> "Error output file"
  , _secs :: w ::: Maybe Int <?> "Timeout"
  , _width :: w ::: Maybe Int <?> "Queue size (Streaming)"
  , _iter :: w ::: Maybe Int <?> "Number of iterations (Streaming)"
  , __fuel :: w ::: Maybe Int <?> "Backtracking fuel"
  , __tries :: w ::: Maybe Int <?> "Reduce the number of children of a node"
  , __depth :: w ::: Maybe Int <?> "Depth bound"
  , __varWeight :: w ::: Maybe Int <?> "Increase weight on variables"
  , __pickTypeOnce :: w ::: Bool <?> "Do not backtrack on choosing a typing constraint to reduce"
  , __showEqualities :: w ::: Bool <?> "Show equality constraints in derivation"
  , __relevance :: w ::: Bool <?> "Variable relevance for Dependent Core"
  , __boring :: w ::: Bool <?> "Generate types"
  , __absurd :: w ::: Bool <?> "Allow parameters of type forall a. a"
  , __pruning :: w ::: Maybe Int <?> "Prune out dead ends"
  , __jumping :: w ::: Maybe Int <?> "Fold linear branches"
  , __iniTerm :: w ::: Maybe String <?> "Initial partial term"
  , __iniType :: w ::: Maybe String <?> "Initial partial type"
  , __noConstants :: w ::: Bool <?> "Disable generating constants"
  , __guessSub :: w ::: Bool <?> "Perform reverse substitutions"
  } deriving Generic

type Options = Options_ Unwrapped

_file :: Options -> String
_file = fromMaybe "decor-log" . _out

instance ParseField RunMode where
instance ParseFields RunMode where
instance ParseRecord RunMode where

instance ParseRecord (Options_ Wrapped) where
  parseRecord = parseRecordWithModifiers lispCaseModifiers

main :: IO ()
main = do
  opts <- unwrapRecord "decor"
  params <- defaultParams opts
  let ?params = params
      ?randomSearchParams = defaultRSP opts
  case _mode opts of
    Gen -> search opts
    RunApp -> runApp opts
    Streaming -> stream opts
    Retry -> retry opts

defaultRSP opts = RandomSearchParams
  { _maxFuel = fromMaybe 100 (__fuel opts)
  , _maxTries = fromMaybe 100 (__tries opts)
  , _maxDepth = fromMaybe 100 (__depth opts)
  , _varWeight = fromMaybe 5 (__varWeight opts)
  , _pickTypeOnce = __pickTypeOnce opts
  }

defaultParams opts = do
  iniT <- for (__iniTerm opts) parse
  iniTy <- for (__iniType opts) parse
  return $ Params
    { _showEqualities = __showEqualities opts
    , _relevance = __relevance opts
    , _boring = __boring opts
    , _absurd = __absurd opts
    , _pruning = fromMaybe 5 (__pruning opts)
    , _jumping = fromMaybe 5 (__jumping opts)
    , _iniTerm = join iniT
    , _iniType = join iniTy
    , _noConstants = __noConstants opts
    , _guessSub = __guessSub opts
    }

parse s = case P.parseDC s of
  Left e -> fail (show e)
  Right r -> return r

stream :: (WithParams, WithRandomSearchParams) => Options -> IO ()
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

streamWith :: WithParams => Maybe Int -> Stream IO S1 -> Handle -> IO ()
streamWith (Just 0) _ _ = return ()
streamWith n (Stream continue) h = do
  x <- continue
  case x of
    Nothing -> return ()
    Just (s, continue) -> do
      hPutStrLn h (showSolution s)
      streamWith (fmap (subtract 1) n) continue h

retry opts = do
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
  tid2 <- forkIO $ loop (fromMaybe 10 (_secs opts))
  let history = do
        xs <- readMVar log
        return $ do
          Just (fuel, s) <- xs
          [   replicate 30 '='
            , show fuel
            , showSolution s
            , showCurrentDerivation s
            ]
  let h BlockedIndefinitelyOnMVar =
        for_ (_eout opts) $ \file -> do
          writeFile file . unlines =<< history
          putStrLn $ "Search sample written to " ++ file
  handle h $ do
    s <- takeMVar result
    xs <- readMVar log
    killThread tid2
    case s of
      Right s -> do
        -- putStrLn "SUCCESS\n"
        -- putStrLn (showSolution s)
        for_ (_out opts) $ \file -> do
          writeFile file $ showCurrentDerivation s
          putStrLn $ "Derivation written to " ++ file
        case treeSolution s of
          Nothing -> do
            putStr "should not happen"
            hFlush stdout
            retry opts
          Just (a, b) -> do
            if typeOf a /= Just b then do
              putStr "TERM: " >> print a
              putStr "TYPE : " >> print (Just b)
              putStr "TYPE': " >> print (typeOf a)
            else if preservation a then
              putStr "," >> hFlush stdout >> retry opts
            else do
              putStr "TERM: " >> print a
              putStr "TYPE: " >> print b
              putStr "STEPS TO: " >> print (step a)
              putStr "OF TYPE: " >> print (typeOf <$> step a)
      Left (e, s) -> do
        for_ (_eout opts) $ \file -> do
          history <- history
          writeFile file . unlines $
            [ "FAIL"
            , showSolution s
            , e
            , showCurrentDerivation s
            ] ++ history
          putStrLn $ "Search state written to " ++ file
        putStr "." >> retry opts


search :: (WithParams, WithRandomSearchParams) => Options -> IO ()
search opts = do
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
  tid2 <- forkIO $ loop (fromMaybe 10 (_secs opts))
  let history = do
        xs <- readMVar log
        return $ do
          Just (fuel, s) <- xs
          [   replicate 30 '='
            , show fuel
            , showSolution s
            , showCurrentDerivation s
            ]
  let h BlockedIndefinitelyOnMVar =
        for_ (_eout opts) $ \file -> do
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
        eval opts s
      Left (e, s) ->
        for_ (_eout opts) $ \file -> do
          history <- history
          writeFile file . unlines $
            [ "FAIL"
            , showSolution s
            , e
            , showCurrentDerivation s
            ] ++ history
          putStrLn $ "Search state written to " ++ file


eval :: t -> S1 -> IO ()
eval opts s =
  case treeSolution s of
    Just (a, b) -> do
      print a
      print b
      print (typeOf a)
      for_ (step a) $ \t -> do
        print (typeOf t)
        print t
      print (preservation a)
    Nothing -> return ()


runApp :: WithParams => Options -> IO ()
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

app :: WithParams => App (NonEmpty (Zs, Int)) () String
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
                str . unlines . fmap showEqn . Map.toList . eqns . constraints
              ) s
              <+>
              ( viewport k_window Both .
                str . unlines . fmap (fromMaybe <$> show <*> showK1 s) . ks1 . constraints
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
          | (_, s, t) : _ <- drop k zs, [("Done", _, _)] <- children s t ->
              continue hs_
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
children _ (Pure s) = [("Done", s, Pure s)]
children s (Free f) = case f of
  Tag _ f@(Free (Tag _ _)) -> [name "Continue" f]
  Tag _ f -> children s f
  Pick d xfs -> [name ("Pick[" ++ d ++ "]" ++ ": " ++ show x) f | (x, f) <- xfs]
  Fail e -> []
  Check t -> children s t
  where
    name n t = (n, fromMaybe s (stateOf t), t)
