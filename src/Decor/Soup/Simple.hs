{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
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
import Data.Char (isSpace)
import Data.Foldable
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Traversable
import Data.Tree
import Data.Typeable
import GHC.Generics (Generic)
import Prelude hiding (fail)

import Decor.Types
import Decor.Soup

data ChoiceF s a
  = Tag s a
  | forall x. (Typeable x, Show x) => Pick String [(x, a)]
  | Fail String

-- deriving instance (Show s, Show a) => Show (ChoiceF s a)
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

runM :: M a -> Free (ChoiceF S1) a
runM (M m) = lowerCodensity (evalStateT m initS1)

instance MonadFail M where
  fail = wrap . Fail

instance MonadFresh M where
  freshI = do
    s <- get
    let i = counter s
    put (s { counter = i + 1 })
    return i

instance MonadSoup M where
  pick d xs = tag >> liftF (Pick d xs) >>= \x -> tag >> return x

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
  | K1Irr DeBruijnV DCId
  | K1_ K1
  deriving (Eq, Ord, Show, Generic)

data IdOrDC = Id_ DCId | DC_ (DCore_ Soup)
  deriving (Eq, Ord, Show)

k1EqId :: DCId -> DCId -> Shift -> DeBruijnV -> K1
k1EqId u v = K1Eq u (Id_ v)

k1EqDC :: DCId -> DCore_ Soup -> K1
k1EqDC u v = K1Eq u (DC_ v) (toEnum 0) (toEnum 0)

ksH1 :: Lens' (S H1) [K1]
ksH1 = l @"ks" . l @"ks"

eqnsH1 :: Lens' (S H1) (Map DCId Alias)
eqnsH1 = l @"ks" . l @"eqns"

ksHistoryH1 :: Lens' (S H1) (Map K1 [K1])
ksHistoryH1 = l @"ks" . l @"history"

updateHistory :: MonadChoice m => K1 -> [K1] -> m ()
updateHistory k ks = ksHistoryH1 %= Map.insert (strip k) (fmap strip ks)
  where
    strip (K1_ k) = strip k
    strip k = k

initS1 :: S1
initS1 = S 0 (H1 Map.empty [k0] Map.empty)

k0 :: K1
k0 = K1Type emptyCtx (DCId (-1)) (DCId (-2))

unfoldH1 :: (WithParams, MonadChoice m) => m S1
unfoldH1 = tag >> instantiateH1 >>= \done ->
  if done then
    get
  else
    reduceH1 >> unfoldH1 >>= \s -> do
      if not absurd then
        absurdCheck s
      else if not boring then
        boringCheck s
      else
        return ()
      return s

type Tree_ s = Free (ChoiceF s) s

treeH1 :: WithParams => Tree_ S1
treeH1 =
  quickPrune 3 .
  collapseTags 10 .
  relevantRelevance .
  runM $
  unfoldH1

relevantRelevance :: WithParams => Free (ChoiceF s) a -> Free (ChoiceF s) a
relevantRelevance
  | relevance = id
  | otherwise = relevantRelevance'

relevantRelevance' :: Free (ChoiceF s) a -> Free (ChoiceF s) a
relevantRelevance' (Free (Pick "Rel" ((_, t) : _))) = relevantRelevance' t
relevantRelevance' (Free f) = Free (fmap relevantRelevance' f)
relevantRelevance' (Pure a) = Pure a

collapseTags :: Int -> Free (ChoiceF s) a -> Free (ChoiceF s) a
collapseTags fuel = everywhere (collapse fuel)
  where
    collapse n (Free (Tag _ t@(Free (Tag _ _)))) | n > 0 = collapse (n-1) t
    collapse _ f = f

quickPrune :: Int -> Free (ChoiceF s) a -> Free (ChoiceF s) a
quickPrune fuel = everywhere (prune fuel)
  where
    prune n (Free f) | n > 0 = Free $ case fmap (prune (n-1)) f of
      Pick d xs ->
        case [(x, a) | (x, a) <- xs, not (isFail a)] of
          [] -> Fail "No good pick"
          xs -> Pick d xs
      Fail s -> Fail s
      Tag _ (Free (Fail e)) -> Fail e
      f -> f
    prune _ t = t
    isFail (Free (Fail _)) = True
    isFail _ = False

everywhere :: Functor f => (Free f a -> Free f a) -> Free f a -> Free f a
everywhere p t =
  case p t of
    Pure a -> Pure a
    Free f -> Free (fmap (everywhere p) f)

instantiateH1 :: (WithParams, MonadChoice m) => m Bool
instantiateH1 = do
  ks <- use ksH1
  picks <- for (focus ks) $ \(k1, ks') ->
    case k1 of
      K1Type ctx t ty -> do
        k1Str <- get <&> \s -> showK1 s k1
        return . Just $
          ( L (fromMaybe "Typing judgement" k1Str)
          , do
              ksH1 .= ks'
              typeCheck ctx t ty >>= traverse andK >>= \ks1' -> do
                let ks1 = concat ks1'
                ksH1 %= (ks1 ++)
                updateHistory k1 ks1
          )
      _ -> return Nothing
  case catMaybes picks of
    [] ->
      if null [() | K1_ _ <- ks] then
        return True
      else do
        ksH1 %= fmap (\k -> case k of K1_ k -> k ; k -> k)
        instantiateH1
    picks -> do
      join $ pick "Type" picks
      return False

{-
  extractKType r = M $ do
    ks <- use ksH1
    (go, ks) <- (lift . lift)
      [ (r ctx t ty, ks)
      | (K1Type ctx t ty, ks) <- focus ks ]
    ksH1 .= ks
    unM go
-}

andK :: MonadChoice m => K -> m [K1]
andK k = return (toK1 k)

toK1 :: K -> [K1]
toK1 (KEqDC t (RHSHead h)) = [k1EqDC t h]
toK1 (KEqDC t (RHSId u n)) = [k1EqId t u n (toEnum 0)]
toK1 (KEqDC t (RHSSub u v)) = [K1Sub t u v (toEnum 0)]
toK1 (KType ctx t u) = [K1Type ctx t u]
toK1 (KRel Rel _) = []
toK1 (KRel Irr u) = [K1Irr (toEnum 0) u]
toK1 (KWF _) = []  -- Handled via redundant constraints
toK1 (K_ k) = fmap K1_ (toK1 k)

-- eqHeadH1 :: DCId -> DCore_ Soup -> Shift -> Shift -> M' H1 [K1]
-- eqHeadH1 t h = do
--   eqns <- use eqnsH1
--   case Map.lookup t eqns of
--     Nothing -> eqnsH1 %= Map.insert t h >> return []
--     Just h' -> eqHeadsH1 h h'

boringCheck :: MonadChoice m => S1 -> m ()
boringCheck s = do
  let K1Type _ _ v = k0
  if unlikeStar (s ^. eqnsH1) v then
    return ()
  else
    fail "Boring type"

unlikeStar :: Map DCId (DCore_ Soup) -> DCId -> Bool
unlikeStar eqns v = case Map.lookup v eqns of
  Nothing -> True
  Just Star -> False
  Just (Pi _ _ _ v') -> unlikeStar eqns v'
  Just _ -> True

absurdCheck :: MonadChoice m => S1 -> m ()
absurdCheck s = do
  let K1Type _ _ v = k0
  if noAbsurdParameters (s ^. eqnsH1) v then
    return ()
  else
    fail "Absurd type"

noAbsurdParameters :: Map DCId (DCore_ Soup) -> DCId -> Bool
noAbsurdParameters eqns v = case Map.lookup v eqns of
  Nothing -> True
  Just Star -> False
  Just (Pi _ () u' v') ->
    notAbsurdType eqns u' && noAbsurdParameters eqns v'
  Just _ -> True

notAbsurdType :: Map DCId (DCore_ Soup) -> DCId -> Bool
notAbsurdType eqns u = loop u (DeBruijnV 0)
  where
    loop u n = case Map.lookup u eqns of
      Nothing -> True
      Just (Pi _ () _ u') -> loop u' (shift n 1)
      Just (Var m) | m < n -> False
      Just _ -> True

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
          , k1EqId b1   b2   n (succ m)
          ]
  (Abs{}, _) -> fail "Abs"

  (Pi rel1 () tyA1 tyB1, Pi rel2 () tyA2 tyB2)
    | rel1 == rel2 ->
        return
          [ k1EqId tyA1 tyA2 n  m
          , k1EqId tyB1 tyB2 n (succ m)
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
refresh h 0 (DeBruijnV 0) _ = return (h, [])
refresh h n m k = case h of
  Star -> return (Star, [])
  Var v
    | v >= m && shift v n < m -> fail "Refresh Var, scope"
    | v >= m -> return (Var (shift v n), [])
    | otherwise -> return (Var v, [])
  Abs rel () tyA b -> do
    (tyA', b') <- freshes
    return (Abs rel () tyA' b', [k tyA tyA' n m, k b b' n (succ m)])
  Pi rel () tyA tyB -> do
    (tyA', tyB') <- freshes
    return (Pi rel () tyA' tyB', [k tyA tyA' n m, k tyB tyB' n (succ m)])
  App b a rel -> do
    (b', a') <- freshes
    return (App b' a' rel, [k b b' n m, k a a' n m])

reduceH1 :: MonadChoice m => m ()
reduceH1 = use ksH1 >>= reduceH1'

reduceH1' :: MonadChoice m => [K1] -> m ()
reduceH1' = loop
  where
    loop ks = tag >> do
      ks' <- fmap concat $ traverse reduceAtomH1_ ks
      ksH1 .= ks'
      if ks /= ks' then
        loop ks'
      else
        return ()

reduceAtomH1_ :: MonadChoice m => K1 -> m [K1]
reduceAtomH1_ k = do
  ks <- reduceAtomH1 k
  case ks of
    [k'] | k == k' -> return ks
    _ -> do
      updateHistory k ks
      return ks

reduceAtomH1 :: MonadChoice m => K1 -> m [K1]
reduceAtomH1 (K1Eq u (Id_ v) 0 (DeBruijnV 0)) | u == v = return []
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
    Just (Var x) | x == n' -> return [k1EqId u w n (toEnum 0)]
    Just h -> do
      (h', ks) <- refresh h (-1) n' $ \v v' _ n' -> K1Sub v' v w n'
      return (k1EqDC u h' : ks)
    Nothing -> case Map.lookup u eqns of
      Just h -> do
        let left = return (Var n', [k1EqId u w n (toEnum 0)])
            right = refresh h 0 (toEnum 0) $ \v v' _ n' -> K1Sub v v' w n'
        (h', ks) <- join $ pick "Sub"
          [ (L "Sub", left)
          , (L "NoSub", right)
          ]
        eqnsH1 %= Map.insert v h'
        return ks
      Nothing -> return [k]
reduceAtomH1 k@(K1Type ctx u v) = do
  eqns <- use eqnsH1
  case Map.lookup u eqns of
    Nothing -> return [k]
    Just h -> fmap (>>= toK1) (typeCheck' ctx v h)
reduceAtomH1 k@(K1Irr n u) = do
  eqns <- use eqnsH1
  case Map.lookup u eqns of
    Nothing -> return [k]
    Just h -> checkIrr n h
reduceAtomH1 (K1_ k) = (fmap . fmap) K1_ (reduceAtomH1 k)

checkIrr :: MonadChoice m => DeBruijnV -> DCore_ Soup -> m [K1]
checkIrr n h = case h of
  Star -> return []
  Var m | n == m -> fail "Irrelevant"
  Var _ -> return []
  Pi _rel () tyA tyB -> return [K1Irr n tyA, K1Irr (shift n 1) tyB]
  Abs _rel () _ b -> return [K1Irr (shift n 1) b]
  App b a _rel -> return [K1Irr n b, K1Irr n a]

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

instance Lns "ks" H1 [K1] where
  l f h = fmap (\ks -> h { ks1 = ks }) (f (ks1 h))

instance Lns "eqns" H1 (Map DCId Alias) where
  l f h = fmap (\eqns -> h { eqns = eqns }) (f (eqns h))

instance Lns "history" H1 (Map K1 [K1]) where
  l f h = fmap (\ksHistory -> h { ksHistory = ksHistory }) (f (ksHistory h))

currentDerivation :: S1 -> Tree K1
currentDerivation = derivationH1 . ksHistory . constraints

derivationH1 :: Map K1 [K1] -> Tree K1
derivationH1 history = unfoldTree f k0
  where
    f k = (k, msum (Map.lookup k history))

showK1 :: WithParams => S1 -> K1 -> Maybe String
showK1 s (K1Type ctx u v) =
  Just
    ( showCtx s ctx ++
      " ⊢ " ++ showDCHead s u ((show u ++ " = ") ++) ++
      " : " ++ showDCHead s v (++ (" = " ++ show v)))
showK1 _ k@(K1Eq{}) | showEqualities = Just (show k)
showK1 s (K1_ k) = fmap parens (showK1 s k)
showK1 _ _ = Nothing

showCtx :: S1 -> Ctx -> String
showCtx _ ctx =
  (intercalate "," . reverse)
    [showDeBruijnV n ++ ":" ++ show u | (n, u) <- zip [DeBruijnV 0 ..] (varCtx ctx)]

showDCHead :: WithParams => S1 -> DCId -> (String -> String) -> String
showDCHead s u cont = case Map.lookup u (s ^. eqnsH1) of
  Just a -> cont (showDCoreSoup a)
  Nothing -> show u

joinTree :: Tree (Maybe a) -> Forest a
joinTree (Node a ts) =
  let ts' = ts >>= joinTree
  in case a of
    Just a -> [Node a ts']
    Nothing -> ts'

showTree :: WithParams => S1 -> Tree K1 -> String
showTree s = drawForest . joinTree . fmap (showK1 s)

showCurrentDerivation :: WithParams => S1 -> String
showCurrentDerivation s = showTree s (currentDerivation s)

showRoot :: Free (ChoiceF s) a -> String
showRoot (Free (Tag _ (Free (Tag _ _)))) = "Continue"
showRoot (Free (Tag _ f)) = showRoot f
showRoot (Free (Fail e)) = "Fail: " ++ e
showRoot (Free (Pick d _)) = "Pick[" ++ d ++ "]"
showRoot (Pure _) = "Done"

showSolution :: WithParams => S1 -> String
showSolution s =
  case k0 of
    K1Type ctx u v ->
      showCtx s ctx ++ " ⊢ " ++ showDCTerm s 0 u ++ " : " ++ showDCTerm s 0 v
    _ -> "assert false"

showDCTerm :: WithParams => S1 -> Int -> DCId -> String
showDCTerm s n u = ("\n" ++) . postProcess 0 [0] $ showDCTerm' s n u

postProcess :: Int -> [Int] -> String -> String
postProcess _ u@(n : _) ('\n' : s) =
  '\n' : replicate n ' ' ++ postProcess n u (dropWhile isSpace s)
postProcess n u ('(' : s) = '(' : postProcess (n+1) (n + 1 : u) s
postProcess n ~(_ : u) (')' : s) = ')' : postProcess (n+1) u s
postProcess n u (c : s) = c : postProcess (n+1) u s
postProcess _ _ [] = []

showDCTerm' :: WithParams => S1 -> Int -> DCId -> String
showDCTerm' s n u = case Map.lookup u (s ^. eqnsH1) of
  Just h -> showDCoreSoup_ (showDCTerm' s) n h ++ "\n"
  Nothing -> show u ++ "\n"

showEqn :: WithParams => (DCId, DCore_ Soup) -> String
showEqn (u, t) = show u ++ " = " ++ showDCoreSoup t
