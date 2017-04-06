{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

import Brick
import Graphics.Vty (Key(..), Event(..), defAttr)

import Control.Concurrent
import Control.Exception
import Control.Monad
import Control.Monad.Free
import Data.Either
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (fromMaybe)
import Options.Generic
import System.Environment (getArgs)
import System.IO
import qualified Data.List.NonEmpty as NonEmpty

import Decor.Soup
import Decor.Soup.Simple
import Decor.Soup.SimpleRandom

data Options = Options
  { _out :: Maybe String
  , _gen :: Bool
  , _secs :: Maybe Int
  } deriving Generic

_file :: Options -> String
_file = fromMaybe "decor-log" . _out

instance ParseRecord Options where
  parseRecord = parseRecordWithModifiers defaultModifiers{fieldNameModifier=tail}

main = do
  opts <- getRecord "decor"
  if _gen opts then
    search opts
  else
    runApp opts

search :: Options -> IO ()
search opts = do
  let fuel = 100
      file = _file opts
  m <- newMVar (fuel, initS1)
  result <- newEmptyMVar
  tid <- forkIO $ runLogS m (randomSearch fuel) >>= putMVar result
  let loop xs 0 = do
        killThread tid
        return xs
      loop xs n = do
        threadDelay (10 ^ 6)
        x <- tryTakeMVar m
        b <- isEmptyMVar result
        if b then do
          loop (x : xs) (n - 1)
        else
          return xs
  xs <- loop [] (fromMaybe 10 (_secs opts))
  let getResult = do
        s <- takeMVar result
        case s of
          Right s -> do
            putStrLn "SUCCESS\n"
            putStrLn (showSolution s)
            writeFile file $ showCurrentDerivation s
            putStrLn $ "Derivation written to " ++ file
          Left (e, s) -> do
            writeFile file . unlines $
              [ "FAIL"
              , e
              , showCurrentDerivation s
              ] ++ history
            putStrLn $ "Search state written to " ++ file
      history = do
        Just (fuel, s) <- xs
        [replicate 30 '=', show fuel, showCurrentDerivation s]
  catch getResult $ \BlockedIndefinitelyOnMVar -> do
    writeFile file . unlines $ history
    putStrLn $ "Search sample written to " ++ file

runApp :: Options -> IO ()
runApp opts = do
  ((zs, k) :| _) <- defaultMain
    app
    (return (children initS1 treeH1, 0))
  case _out opts of
    Nothing -> return ()
    Just file ->
      level zs k (return ()) $ \_ s _ -> do
        writeFile file $ showCurrentDerivation s
        putStrLn $ "Derivation written to " ++ file

type Zs = [(String, S1, Tree_ S1)]

main_window = "main"

level :: Zs -> Int -> r -> (String -> S1 -> Tree_ S1 -> r) -> r
level zs k r cont = case drop k zs of
  (key, s, t) : _ -> cont key s t
  _ -> r

app :: App (NonEmpty (Zs, Int)) () String
app = App
  { appDraw = \history@((zs, k) :| _) ->
      level zs k [str "[]"] $ \key s t ->
        [ viewport main_window Both
            (str (showCurrentDerivation s))
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
          <=> (vLimit 5 . str . show . ks1 . constraints $ s)
        ]
  , appChooseCursor = \_ _ -> Nothing
  , appHandleEvent = \hs_@((zs, k) :| hs) e -> case e of
      VtyEvent e -> case e of
        EvKey (KChar 'h') [] -> hScrollBy scr (-1) >> continue hs_
        EvKey (KChar 'j') [] -> vScrollBy scr 1 >> continue hs_
        EvKey (KChar 'k') [] -> vScrollBy scr (-1) >> continue hs_
        EvKey (KChar 'l') [] -> hScrollBy scr 1 >> continue hs_
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
       where scr = viewportScroll main_window
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
