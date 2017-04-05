{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Decor.Soup.Trivial where

import Control.Applicative
import Control.Comonad.Cofree
import Control.Monad.Except
import Control.Monad.Fail
import Control.Monad.State.Strict
import Data.Foldable

import Decor.Soup

type ForkF = ExceptT () []

newtype M h a = M { unM :: M' h a }
  deriving (Functor, Applicative, Monad, MonadState (S h))

instance Alternative (M h) where
  empty = (M . mapStateT unSkip . lift) empty
  M a <|> M b = (M . mapStateT unSkip)
    (mapStateT Skip a <|> mapStateT Skip b)

type M' h = StateT (S h) ForkF

instance MonadFresh (M h) where
  freshI = state $ \s ->
    let i = counter s in (i, s {counter = i+1})

instance MonadSoup (M h) where
  pick _ = M . lift . lift . fmap snd

instance MonadFail (M h) where
  fail _ = M . lift . ExceptT . return $ Left ()

runM :: KStore h => M h [K] -> S h -> ForkF (S h)
runM = execStateT . unM . (>>= andKs)

class KStore h where
  initStore :: h
  andK :: K -> M h ()
  reduce :: M h ()
  extractKType :: (Ctx -> DCId -> DCId -> M h a) -> M h a

  andKs :: [K] -> M h ()
  andKs = traverse_ andK


generate :: KStore h => (Cofree ForkF (S h), (DCId, DCId))
generate = (coiter (runM (extractKType typeCheck)) s0, tt0)
  where
    ExceptT [Right (tt0, s0)] =
      ((`runStateT` s) . unM)
        (initK >>= \(ks, t, ty) -> andKs ks >> reduce >> return (t, ty))
    s = S 0 initStore

tree :: KStore h => Cofree ForkF (S h)
tree = fst generate

data Elide f a = X | Y (f a)
  deriving (Eq, Ord, Show, Foldable, Functor)

takeDepth :: Int -> Cofree ForkF a -> Cofree (Elide ForkF) a
takeDepth n (a :< f) = a :< takeDepth' n f
  where
    takeDepth' 0 _ = X
    takeDepth' n f = Y (fmap (takeDepth (n - 1)) f)
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
