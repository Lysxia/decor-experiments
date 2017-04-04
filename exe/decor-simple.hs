import Brick
import Graphics.Vty (Key(..), Event(..), defAttr)

import Control.Monad.Free
import Data.Either
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty

import Decor.Soup
import Decor.Soup.Simple

main = defaultMain
  app
  (return (children treeH1, 0))

type Zs = [(String, Either String S1, Tree_ S1)]

main_window = "main"

app :: App (NonEmpty (Zs, Int)) () String
app = App
  { appDraw = \((zs, k) :| _) ->
      [ viewport main_window Both $
          case drop k zs of
            (key, z, _) : _  ->
              str (show k ++ ": " ++ key) <=>
              str (either id showCurrentDerivation z)
            [] -> str "[]"
      ]
  , appChooseCursor = \_ _ -> Nothing
  , appHandleEvent = \s@((zs, k) :| hs) e -> case e of
      VtyEvent e -> case e of
        EvKey (KChar 'h') [] -> hScrollBy scr (-1) >> continue s
        EvKey (KChar 'j') [] -> vScrollBy scr 1 >> continue s
        EvKey (KChar 'k') [] -> vScrollBy scr (-1) >> continue s
        EvKey (KChar 'l') [] -> hScrollBy scr 1 >> continue s
        EvKey KUp   []
          | Just hs' <- NonEmpty.nonEmpty hs ->
              continue hs'
        EvKey KDown []
          | (_, _, t) : _ <- drop k zs ->
              continue (NonEmpty.cons (children t, 0) s)
        EvKey KLeft  []
          | k > 0 ->
              continue ((zs, k - 1) :| hs)
        EvKey KRight []
          | k < length zs - 1 ->
              continue ((zs, k + 1) :| hs)
        EvKey (KChar 'q') [] -> halt s
        _ -> continue s
       where scr = viewportScroll main_window
      _ -> continue s
  , appStartEvent = return
  , appAttrMap = const (attrMap defAttr [])
  }

progress :: Int -> Either String s -> Tree_ s -> (Either String s, Tree_ s)
progress 0 z t = (z, t)
progress _ _ t@(Pure s) = (Right s, t)
progress fuel z t@(Free f) = case f of
  Tag s f -> progress (fuel - 1) (Right s) f
  Inst _ -> (z, t)
  Pick _ -> (z, t)
  Fail e -> (Left e, t)

children :: Tree_ s -> [(String, Either String s, Tree_ s)]
children (Pure s) = []
children (Free f) = case f of
  Tag s f -> [name "Checkpoint" f]
  Inst fs -> [name "Inst" f | f <- fs]
  Pick xfs -> [name ("Pick[" ++ x ++ "]") f | (x, f) <- xfs]
  Fail e -> []
  where
    progress' = progress 10 (Left "Progress")
    name n t = let (a, b) = progress' t in (n, a, b)
