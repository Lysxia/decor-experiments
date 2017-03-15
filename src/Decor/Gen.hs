-- | Random generation, with narrowing and backtracking.

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}

module Decor.Gen where

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans.Class
import Data.STRef hiding (writeSTRef)
import QuickCheck.GenT hiding (MonadGen)
import qualified QuickCheck.GenT as GenT

class (Monad m, Alternative m) => MonadGen m where
  data URef m :: * -> *  -- Unifiable reference
  newInteger :: m Integer
  newRef :: m (URef m a)
  getRef :: URef m a -> m (Maybe a)
  setRef :: URef m a -> a -> m ()
  mergeRef :: URef m a -> URef m a -> m ()
  bindRef :: URef m a -> (a -> m ()) -> m ()
  choose :: [(Int, a)] -> m a

ref :: MonadGen m => a -> m (URef m a)
ref a = newRef >>= \r -> setRef r a *> return r

type G s a = GenT (ST s) a

data S = S
  { fuel :: !Int
  , counter :: !Integer
  }

newtype Gen r s a = Gen
  { unGen
      :: (a -> (S -> G s r) -> S -> G s r)
      -> (S -> G s r)
      -> S
      -> G s r
  }

liftG :: G s a -> Gen r s a
liftG ma = Gen $ \ k fail s ->
  ma >>= \ a -> k a fail s

liftGST :: ST s a -> Gen r s a
liftGST = liftG . lift

instance Functor (Gen r s) where
  fmap = liftA

instance Applicative (Gen r s) where
  pure a = Gen $ \ k -> k a
  (<*>) = ap

instance Monad (Gen r s) where
  ma >>= f = Gen $ \ k fail s ->
    unGen ma
      (\ a fail s -> unGen (f a) k fail s)
      fail s

instance Alternative (Gen r s) where
  empty = Gen $ \ _ fail s -> fail s{ fuel = fuel s - 1 }
  ma <|> ma' = Gen $ \ k fail s ->
    let
      fail' s | fuel s == 0 = fail s
      fail' s = unGen ma' k fail s
    in
      unGen ma k fail' s

failing :: Gen r s a -> ST s () -> Gen r s a
failing ma cleanup = Gen $ \ k fail s ->
  let
    fail' s = lift cleanup >> fail s
  in
    unGen ma k fail' s

data Unknown r s a
  = Unknown (a -> Gen r s ())
  | Known a

data Alias r s a
  = Alias (STRef s (Alias r s a))
  | Root !Int (Unknown r s a)

maybeUnk :: Unknown r s a -> Maybe a
maybeUnk (Known a) = Just a
maybeUnk (Unknown _) = Nothing

getRef' :: STRef s (Alias r s a) -> Gen r s (STRef s (Alias r s a), Int, Unknown r s a)
getRef' = liftGST . getRef''

getRef'' :: STRef s (Alias r s a) -> ST s (STRef s (Alias r s a), Int, Unknown r s a)
getRef'' r = do
  r_ <- readSTRef r
  case r_ of
    Root n u -> return (r, n, u)
    Alias r' -> getRef'' r'

instance MonadGen (Gen r s) where
  newtype URef (Gen r s) a = GenURef (STRef s (Alias r s a))

  newInteger = Gen $ \ k fail s ->
    let
      i = counter s
      !s' = s { counter = i + 1 }
    in
      k i fail s'

  newRef = liftGST (GenURef <$> newSTRef (Root 1 (Unknown (\ _ -> return ()))))

  getRef (GenURef r) = maybeUnk . t3 <$> getRef' r
    where t3 (_, _, c) = c

  setRef (GenURef r) a = do
    (r', n, a_) <- getRef' r
    writeRef r' (Root n (Known a))
    case a_ of Unknown k -> k a ; Known _ -> return ()

  mergeRef (GenURef r) (GenURef s) = do
    a_@(_, n, _) <- getRef' r
    b_@(_, m, _) <- getRef' s
    let ((r0, n0, a0), (s0, m0, _)) | n > m = (a_, b_) | otherwise = (b_, a_)
    writeRef s0 (Alias r0)
    writeRef r0 (Root (n0 + m0) a0)

  bindRef (GenURef r) k = do
    (r0, n, a') <- getRef' r
    case a' of
      Unknown k' -> writeRef r0 (Root n (Unknown (liftA2 (>>) k k')))
      Known a -> k a

  choose xs = choose_ totalW xs
    where
      totalW = sum [ w | (w, _) <- xs ]

choose_ :: Int -> [(Int, a)] -> Gen r s a
choose_ 0 _ = empty
choose_ totalW xs = do
  w0 <- liftG (GenT.choose (0, totalW - 1))
  let (w, x, xs') = select w0 id xs
  return x <|> choose_ (totalW - w) xs'
  where
    select w0 k ((w, x) : xs)
      | w < w0 = (w, x, k xs)
      | otherwise = select w0 (k . ((w, x) :)) xs

writeSTRef r = modifySTRef' r . const

writeRef r a = do
  a0 <- liftGST (readSTRef r)
  liftGST (writeSTRef r a)
    `failing` writeSTRef r a0
