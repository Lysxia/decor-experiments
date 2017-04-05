{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}

module Decor.Soup.Simple where

import Control.Applicative
import Control.Monad.Codensity
import Control.Monad.Fail
import Control.Monad.Free
import Control.Monad.State.Strict hiding (fail)
import Lens.Micro.Platform
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Tree
import Data.Typeable
import GHC.Generics (Generic)
import Prelude hiding (fail)

import Decor.Types
import Decor.Soup

data ChoiceF s a
  = Tag s a
  | Inst [a]
  | Pick [(String, a)]
  | Fail String
  deriving Generic

deriving instance (Show s, Show a) => Show (ChoiceF s a)
deriving instance Functor (ChoiceF s)

-- pick :: (Eq x, Show x, Typeable x) => [x] -> (x -> a) -> ChoiceF s a
-- pick xs f = Pick [(x, f x) | x <- xs]

type MonadChoice m =
  ( MonadFree (ChoiceF S1) m
  , MonadState S1 m
  , MonadFresh m
  , MonadFail m
  , MonadSoup m
  )

tag :: MonadChoice m => m ()
tag = get >>= \s -> wrap (Tag s (return ()))

newtype M a = M { unM :: StateT S1 (Codensity (Free (ChoiceF S1))) a }
  deriving (Functor, Applicative, Monad, MonadState S1, MonadFree (ChoiceF S1))

runM :: M () -> Free (ChoiceF S1) S1
runM (M m) = lowerCodensity (execStateT m initS1)

instance MonadFail M where
  fail = wrap . Fail

instance MonadFresh M where
  freshI = do
    s <- get
    let i = counter s
    put (s { counter = i + 1 })
    return i

instance MonadSoup M where
  pick xs = liftF (Inst xs)

type S1 = S H1

type Alias = DCore_ Soup

data H1 = H1
  { eqns :: Map DCId Alias
  , ks1 :: [K1]
  , ksHistory :: Map K1 [K1]
  } deriving (Generic, Show)

data K1
  = K1Eq DCId IdOrDC Shift DeBruijnV
    -- ^ @u = v^n_m@ shift all indices >= m by n
    -- n can be negative!

  | K1Sub DCId DCId DCId DeBruijnV
    -- ^ @u = v[w^n/n]@ substitute

  | K1Type Ctx DCId DCId
  | K1Rel Rel DeBruijnV DCId
  | K1WF Ctx
  deriving (Eq, Ord, Show, Generic)

data IdOrDC = Id_ DCId | DC_ (DCore_ Soup)
  deriving (Eq, Ord, Show)

k1EqId :: DCId -> DCId -> Shift -> DeBruijnV -> K1
k1EqId u v = K1Eq u (Id_ v)

k1EqDC :: DCId -> DCore_ Soup -> K1
k1EqDC u v = K1Eq u (DC_ v) 0 0

ksH1 :: Lens' (S H1) [K1]
ksH1 = l @"ks" . l @"ks"

eqnsH1 :: Lens' (S H1) (Map DCId Alias)
eqnsH1 = l @"ks" . l @"eqns"

ksHistoryH1 :: Lens' (S H1) (Map K1 [K1])
ksHistoryH1 = l @"ks" . l @"history"

initS1 :: S1
initS1 = S 0 (H1 Map.empty [k0] Map.empty)

k0 :: K1
k0 = K1Type emptyCtx (DCId (-1)) (DCId (-2))

unfoldH1 :: MonadChoice m => m ()
unfoldH1 = forever (instantiateH1 >> reduceH1 >> tag)

type Tree_ s = Free (ChoiceF s) s

treeH1 :: Tree_ S1
treeH1 = runM unfoldH1

instantiateH1 :: MonadChoice m => m ()
instantiateH1 = do
  ks <- use ksH1
  eqns <- use eqnsH1
  wrap . Inst $ do
    (K1Type ctx t ty, ks) <- focus ks
    guard (Map.notMember t eqns)
    return $
      typeCheck ctx t ty >>= traverse_ andK

{-
  extractKType r = M $ do
    ks <- use ksH1
    (go, ks) <- (lift . lift)
      [ (r ctx t ty, ks)
      | (K1Type ctx t ty, ks) <- focus ks ]
    ksH1 .= ks
    unM go
-}

andK :: MonadChoice m => K -> m ()
andK = andKH1 >=> \ks -> ksH1 %= (ks ++)

andKH1 :: MonadChoice m => K -> m [K1]
andKH1 (KEqDC t (RHSHead h)) = return [k1EqDC t h]
andKH1 (KEqDC t (RHSId u n)) = return [k1EqId t u n 0]
andKH1 (KEqDC t (RHSSub u v)) = return [K1Sub t u v 0]
andKH1 (KType ctx t u) = return [K1Type ctx t u]
andKH1 (KRel rel u) = return [K1Rel rel 0 u]
andKH1 (KWF ctx) = return [K1WF ctx]
andKH1 (K_ k) = andKH1 k

-- eqHeadH1 :: DCId -> DCore_ Soup -> Shift -> Shift -> M' H1 [K1]
-- eqHeadH1 t h = do
--   eqns <- use eqnsH1
--   case Map.lookup t eqns of
--     Nothing -> eqnsH1 %= Map.insert t h >> return []
--     Just h' -> eqHeadsH1 h h'

eqHeadsH1 :: MonadChoice m => DCore_ Soup -> DCore_ Soup -> Shift -> DeBruijnV -> m [K1]
eqHeadsH1 e1 e2 n m = case (e1, e2) of

  (Star, Star) -> return []
  (Star, _) -> fail "Star"

  (Var v1, Var v2)
    | v2 >= m && shift v2 n < m -> fail "Var, scope"
    | if v2 >= m then v1 == shift v2 n else v1 == v2 ->
        return []
  (Var{}, _) -> fail "Var"

  (Abs rel1 () tyA1 b1, Abs rel2 () tyA2 b2)
    | rel1 == rel2 ->
        return
          [ k1EqId tyA1 tyA2 n  m
          , k1EqId b1   b2   n (m+1)
          ]
  (Abs{}, _) -> fail "Abs"

  (Pi rel1 () tyA1 tyB1, Pi rel2 () tyA2 tyB2)
    | rel1 == rel2 ->
        return
          [ k1EqId tyA1 tyA2 n  m
          , k1EqId tyB1 tyB2 n (m+1)
          ]
  (Pi{}, _) -> fail "Pi"

  (App b1 a1 rel1, App b2 a2 rel2)
    | rel1 == rel2 ->
      return
        [ k1EqId b1 b2 n m
        , k1EqId a1 a2 n m
        ]
  (App{}, _) -> fail "App"

refresh
  :: MonadChoice m
  => DCore_ Soup -> Shift -> DeBruijnV
  -> (DCId -> DCId -> Shift -> DeBruijnV -> K1)
  -> m (DCore_ Soup, [K1])
refresh h 0 0 _ = return (h, [])
refresh h n m k = case h of
  Star -> return (Star, [])
  Var v
    | v >= m && shift v n < m -> fail "Refresh Var, scope"
    | v >= m -> return (Var (shift v n), [])
    | otherwise -> return (Var v, [])
  Abs rel () tyA b -> do
    (tyA', b') <- freshes
    return (Abs rel () tyA' b', [k tyA tyA' n m, k b b' n (m+1)])
  Pi rel () tyA tyB -> do
    (tyA', tyB') <- freshes
    return (Pi rel () tyA' tyB', [k tyA tyA' n m, k tyB tyB' n (m+1)])
  App b a rel -> do
    (b', a') <- freshes
    return (App b' a' rel, [k b b' n m, k a a' n m])

reduceH1 :: MonadChoice m => m ()
reduceH1 = use ksH1 >>= reduceH1'

reduceH1' :: MonadChoice m => [K1] -> m ()
reduceH1' = loop
  where
    loop ks = do
      ks' <- fmap concat $ traverse reduceAtomH1_ ks
      if ks /= ks' then
        loop ks'
      else
        ksH1 .= ks'

reduceAtomH1_ :: MonadChoice m => K1 -> m [K1]
reduceAtomH1_ k = do
  ks <- reduceAtomH1 k
  case ks of
    [k'] | k == k' -> return ks
    _ -> do
      ksHistoryH1 %= Map.insert k ks
      return ks

reduceAtomH1 :: MonadChoice m => K1 -> m [K1]
reduceAtomH1 (K1Eq u (Id_ v) 0 0) | u == v = return []
reduceAtomH1 k@(K1Eq u (Id_ v) n m) = do
  eqns <- use eqnsH1
  case (Map.lookup u eqns, Map.lookup v eqns) of
    (Nothing, Nothing) -> return [k]
    (Just h, Just h') -> eqHeadsH1 h h' n m
    (Nothing, Just h') -> return [K1Eq u (DC_ h') n m]
    (Just h, Nothing) -> return [K1Eq v (DC_ h) (-n) m]
reduceAtomH1 (K1Eq u (DC_ h) n m) = do
  eqns <- use eqnsH1
  case Map.lookup u eqns of
    Nothing -> do
      (h', ks) <- refresh h n m k1EqId
      eqnsH1 %= Map.insert u h'
      return ks
    Just h0 -> eqHeadsH1 h0 h n m
reduceAtomH1 k@(K1Sub u v w n') = do
  let DeBruijnV n = n'
  eqns <- use eqnsH1
  case Map.lookup v eqns of
    Just (Var x) | x == n' -> return [k1EqId u w n 0]
    Just h -> do
      (h', ks) <- refresh h (-1) n' $ \v v' _ n' -> K1Sub v' v w n'
      return (k1EqDC u h' : ks)
    Nothing -> case Map.lookup u eqns of
      Just h -> do
        let left = return (Var n', [k1EqId u w n 0])
            right = refresh h 0 0 $ \v v' _ n' -> K1Sub v v' w n'
        (h', ks) <- wrap $ Pick
          [ ("Sub", left)
          , ("NoSub", right)
          ]
        eqnsH1 %= Map.insert v h'
        return ks
      Nothing -> return [k]
reduceAtomH1 k = return [k]


-- DCId DCId Shift Shift           -- ^ @u = v^n_m@ shift all indices >= m by n
--   | K1Sub DCId DCId DeBruijnV DCId       -- ^ @u = v[w^n/n]@ substitute
--   | K1Type Ctx DCId DCId
--   | K1Rel Rel DeBruijnV DCId
--   | K1WF Ctx

{-

type RetryFlag = Bool

type CollectRetryCont a = [K] -> RetryFlag -> M' H1 a
type CollectRetry =
  forall a. CollectRetryCont a -> K -> M' H1 a

traverseCollectRetry
  :: CollectRetry
  -> [K]
  -> M' H1 [K]
traverseCollectRetry = traverseCollectRetry' []

traverseCollectRetry' :: [K] -> CollectRetry -> [K] -> M' H1 [K]
traverseCollectRetry' acc _collect [] = return acc
traverseCollectRetry' acc collect (k : ks) =
  (`collect` k) $ \moreKs retryFlag ->
    if retryFlag then
      traverseCollectRetry collect (moreKs ++ acc ++ ks)
    else
      traverseCollectRetry' (moreKs ++ acc) collect ks

reduceH1Atom :: CollectRetry
reduceH1Atom ret (KEqDC t (RHSId u shift)) = reduceH1EqDCId t u shift >> ret [] False
reduceH1Atom ret (KEqDC t (RHSHead f)) = reduceH1EqHead t f >> ret [] False
reduceH1Atom ret (KEqDC t (RHSSub tyA tyB)) =
  undefined -- reduceH1EqSub ret t x tyA tyB

reduceH1EqHead :: DCId -> DCore_ Soup -> M' H1 ()
reduceH1EqHead t f = do
  t_ <- lookupH1V t
  case t_ of
    Left t -> eqHead t f
    Right (_, e) -> reduceH1EqHeads' e f

reduceH1EqDCId :: DCId -> DCId -> M' H1 ()
reduceH1EqDCId t u = do
  t_ <- lookupH1V t
  u_ <- lookupH1V u
  case (t_, u_) of
    (Left t, Left u) | t == u -> return ()
    (Left t, Left u) -> alias t u
    (Left t, Right (_, f)) -> eqHead t f
    (Right (_, e), Left u) -> eqHead u e
    (Right (t, _), Right (u, _)) | t == u -> return ()
    (Right (_, e), Right (_, f)) ->
      reduceH1EqHeads' e f

eqHead :: DCId -> DCore_ Soup -> M' H1 ()
eqHead t e = do
  occursCheck' t e
  eqnsH1 %= Map.insert t (Head e)

occursCheck' :: DCId -> DCore_ Soup -> M' H1 ()
occursCheck' t e = case e of
  Star -> return ()
  Var _ -> return ()
  Abs _ _ tyA b -> mapM_ (occursCheck t) [tyA, b]
  Pi _ _ tyA tyB -> mapM_ (occursCheck t) [tyA, tyB]
  App b a _ -> mapM_ (occursCheck t) [b, a]

occursCheck :: DCId -> DCId -> M' H1 ()
occursCheck t u = do
  u_ <- lookupH1V u
  case u_ of
    Left u -> when (t == u) empty
    Right (u, f) -> do
      when (t == u) empty
      occursCheck' t f

alias :: DCId -> DCId -> M' H1 ()
alias t u = eqnsH1 %= Map.insert t (Alias u)

lookupH1V :: DCId -> M' H1 (Either DCId (DCId, DCore_ Soup))
lookupH1V t = do
  s <- get
  case Map.lookup t (s ^. eqnsH1) of
    Just (Alias v) -> lookupH1V v
    Nothing -> return (Left t)
    Just (Head e) -> return (Right (t, e))
-}

instance L "ks" H1 [K1] where
  l f h = fmap (\ks -> h { ks1 = ks }) (f (ks1 h))

instance L "eqns" H1 (Map DCId Alias) where
  l f h = fmap (\eqns -> h { eqns = eqns }) (f (eqns h))

instance L "history" H1 (Map K1 [K1]) where
  l f h = fmap (\ksHistory -> h { ksHistory = ksHistory }) (f (ksHistory h))

currentDerivation :: S1 -> Tree K1
currentDerivation = derivationH1 . ksHistory . constraints

derivationH1 :: Map K1 [K1] -> Tree K1
derivationH1 history = unfoldTree f k0
  where
    f k = (k, msum (Map.lookup k history))

showK1 :: S1 -> K1 -> Maybe String
showK1 s (K1Type ctx u v) =
  Just (showCtx s ctx ++ "|-" ++ showDCHead s u ++ ":" ++ showDCHead s v)
showK1 _ _ = Nothing

showCtx _ _ = "_"

showDCHead s u = case Map.lookup u (s ^. eqnsH1) of
  Just a -> showDCoreSoup a
  Nothing -> show u

joinTree :: Tree (Maybe a) -> Forest a
joinTree (Node a ts) =
  let ts' = ts >>= joinTree
  in case a of
    Just a -> [Node a ts']
    Nothing -> ts'

showTree :: S1 -> Tree K1 -> String
showTree s = drawForest . joinTree . fmap (showK1 s)

showCurrentDerivation :: S1 -> String
showCurrentDerivation s = showTree s (currentDerivation s)
