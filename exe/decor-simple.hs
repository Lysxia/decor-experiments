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
  (return (children initS1 treeH1, 0))

type Zs = [(String, S1, Tree_ S1)]

main_window = "main"

level :: Zs -> Int -> r -> (String -> S1 -> Tree_ S1 -> r) -> r
level zs k r cont = case drop k zs of
  (key, s, t) : _ -> cont key s t
  _ -> r

app :: App (NonEmpty (Zs, Int)) () String
app = App
  { appDraw = \history@((zs, k) :| _) ->
      [ level zs k (str "[]") $ \key s t ->
          viewport main_window Both
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

progress :: Int -> s -> Tree_ s -> (s, Tree_ s)
progress 0 s t = (s, t)
progress _ _ t@(Pure s) = (s, t)
progress fuel s t@(Free f) = case f of
  Tag s f -> progress (fuel - 1) s f
  Pick _ _ -> (s, t)
  Fail _ -> (s, t)

children :: s -> Tree_ s -> [(String, s, Tree_ s)]
children _ (Pure s) = []
children s (Free f) = case f of
  Tag s f -> [name "Continue" f]
  Pick d xfs -> [name ("Pick[" ++ d ++ "]" ++ ": " ++ show x) f | (x, f) <- xfs]
  Fail e -> []
  where
    progress' = progress 10 s
    name n t = let (a, b) = progress' t in (n, a, b)
