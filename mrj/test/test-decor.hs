{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

import Control.Applicative
import Control.Monad

import Generics.OneLiner

import Test.HUnit
import qualified Test.QuickCheck.Gen as QC
import qualified Test.QuickCheck.Random as QC

import Decor.Gen

g0 :: QC.QCGen
g0 = QC.mkQCGen 1337

runGen' :: (forall s. Gen (Maybe a) s a) -> Maybe a
runGen' m = QC.unGen (runGen m) g0 100

tests :: Test
tests = TestList
  [ testNewInteger
  , testNewRef
  , testSetRef
  , testMergeRef
  , testBindRef
  , testSetRefFail
  , testMergeRefFail
  , testBindRefFail
  , testBindRefFail2
  ]

testNewInteger = "newInteger" ~:
  Just (0, 1) ~=? runGen' (liftA2 (,) newInteger newInteger)

testNewRef = "newRef" ~:
  Just (Nothing :: Maybe ()) ~=? runGen' (newRef >>= getRef)

testSetRef = "setRef" ~:
  Just (Just ()) ~=? runGen' (do
    r <- newRef
    setRef r ()
    getRef r)

testMergeRef = "mergeRef" ~:
  Just (Just ()) ~=? runGen' (do
    (r, s) <- multiRef [()]
    mergeRef r s
    setRef s ()
    getRef r)

testBindRef = "bindRef" ~:
  Just (Just (), Nothing) ~=? runGen' (do
    (r, s, t, u) <- multiRef [()]
    bindRef r $ \ () -> setRef t ()
    bindRef s $ \ () -> setRef u ()
    setRef r ()
    liftA2 (,) (getRef t) (getRef u))

testSetRefFail = "setRefFail" ~:
  Just Nothing ~=? runGen' (do
    r <- newRef
    (setRef r () >> empty) <|> getRef r)

testMergeRefFail = "mergeRefFail" ~:
  Just (Nothing, Nothing) ~=? runGen' (do
    (r, s, t, u) <- multiRef [()]
    setRef r ()
    (mergeRef r t >> mergeRef s u >> setRef s () >> empty)
      <|> liftA2 (,) (getRef t) (getRef u))

testBindRefFail = "bindRefFail" ~:
  Just Nothing ~=? runGen' (do
    (r, s) <- multiRef [()]
    bindRef r $ \ () -> setRef s ()
    (setRef r () >> empty) <|> getRef s)

testBindRefFail2 = "bindRefFail2" ~:
  Just (Nothing, Nothing, Nothing) ~=? runGen' (do
    (r, s, t, u) <- multiRef [()]
    bindRef r $ \ () -> setRef s ()
    bindRef r $ \ () -> setRef t () >> empty
    bindRef r $ \ () -> setRef u ()
    let x = liftA3 (,,) (getRef s) (getRef t) (getRef u)
    (setRef r () >> x) <|> x)

main :: IO ()
main = void $ runTestTT tests

multiRef
  :: forall a t r s c proxy
  .  (ADT t, Constraints t c, c ~ ((~) (URef (Gen r s) a)))
  => proxy a -> Gen r s t
multiRef _ = createA (For :: For c) newRef

