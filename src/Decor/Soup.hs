{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Decor.Soup where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Writer

import Control.Comonad.Cofree

import Data.Foldable

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap

import Lens.Micro.Platform

import Generics.OneLiner
import GHC.Generics (Generic)
import GHC.TypeLits

import Decor.Types

data Soup

type instance RelT Soup = Rel
type instance FunT Soup = FunId
type instance VarT Soup = VarId
type instance BindVarT Soup = VarId
type instance CVarT Soup = VarId
type instance BindCVarT Soup = CVarId
type instance DCore Soup = DCId
type instance Coercion Soup = CoercionId

newtype DCId = DCId Integer
  deriving (Eq, Ord, Show)

newtype CoercionId = CoercionId Integer
  deriving (Eq, Ord, Show)

-- | Constraints.
data K where
  KEqDC :: DCId -> RHS -> K
  -- ^ @t = u[sub]@. Term equality.

  KType :: Ctx -> DCId -> DCId -> K
  -- ^ @G |- t : u@. Typing judgement.

  KTypeC :: Ctx -> Ctx' -> CoercionId -> EqProp DCId -> K
  -- ^ @G |- g : a ~ b@. Coercion typing judgement.

  KRel :: Rel -> VarId -> DCId -> K
  -- ^ @r & x <- |t|@. Relevance check.

  KWF :: Ctx -> K
  -- ^ @|- G@. Well-formed context.

  KOK :: Ctx -> EqProp DCId -> K
  -- ^ @G |- phi OK@. Well-formed equality proposition.

  K_ :: K -> K
  -- ^ Redundant constraints.

  deriving (Eq, Show)

kEqDC :: DCId -> RHS -> K
kEqDC = KEqDC

data Sub = Sub
  { vSub :: Bimap VarId VarId
  , cSub :: Bimap CVarId CVarId
  } deriving (Eq, Show)

emptySub :: Sub
emptySub = Sub Bimap.empty Bimap.empty

isEmptySub :: Sub -> Bool
isEmptySub = (== emptySub)

subV :: VarId -> Sub -> Maybe VarId
subV v = Bimap.lookup v . vSub

insertSub :: VarId -> VarId -> Sub -> Sub
insertSub v1 v2 sub = sub { vSub = Bimap.insert v1 v2 (vSub sub) }

invSub :: Sub -> Sub
invSub (Sub vs cs) = Sub (Bimap.twist vs) (Bimap.twist cs)

composeBimap :: (Ord b, Ord c) => Bimap a b -> Bimap b c -> Bimap a c
composeBimap ma mb = Bimap.mapR (mb Bimap.!) ma

composeSub :: Sub -> Sub -> Sub
composeSub (Sub vs cs) (Sub vs' cs') =
  Sub (composeBimap vs vs') (composeBimap cs cs')

newtype UnionFind a = UnionFind { unUF :: Map a (Either Int a) }
  deriving Show

emptyUF :: UnionFind a
emptyUF = UnionFind Map.empty

rootUF :: Ord a => a -> UnionFind a -> a
rootUF a uf = rootUF' a uf $ \a' _ _ -> a'

rootUF'
  :: Ord a
  => a -> UnionFind a -> (a -> Int -> (a -> UnionFind a -> UnionFind a) -> r) -> r
rootUF' a uf k =
  case Map.lookup a (unUF uf) of
    Nothing -> k a 1 h
    Just (Left n) -> k a n h
    Just (Right a') -> rootUF' a' uf $ \a0 n0 k0 -> k a0 n0 $ \a' -> k0 a' . h a'
  where
    h a' = UnionFind . Map.insert a (Right a') . unUF

mergeUF :: Ord a => a -> a -> UnionFind a -> UnionFind a
mergeUF a b = snd . mergeUF' a b

mergeUF' :: Ord a => a -> a -> UnionFind a -> (a, UnionFind a)
mergeUF' a b uf =
  rootUF' a uf $ \a' n updateA ->
    rootUF' b uf $ \b' m updateB ->
      let
        merge c =
          (,) c . UnionFind . Map.insert c (Left (n + m)) . unUF . updateA c . updateB c
      in
        merge (if n > m then a' else b') uf

equalUF :: Ord a => a -> a -> UnionFind a -> Bool
equalUF a b uf =
  rootUF' a uf $ \a _ _ -> rootUF' b uf $ \b _ _ ->
    a == b

data RHS
  = RHSId DCId
  | RHSHead (DCore_ Soup)
  | RHSSub VarId DCId DCId
  | RHSSubC CVarId CoercionId DCId
  deriving (Eq, Ord, Show)

class (Monad m, Fresh m Integer) => MonadSoup m where
  pick :: [a] -> m a

class Applicative m => Fresh m a where
  fresh :: m a

instance (Applicative m, Fresh m Integer) => Fresh m VarId where
  fresh = VarId <$> fresh

instance (Applicative m, Fresh m Integer) => Fresh m CVarId where
  fresh = CVarId <$> fresh

instance (Applicative m, Fresh m Integer) => Fresh m DCId where
  fresh = DCId <$> fresh

instance (Applicative m, Fresh m Integer) => Fresh m CoercionId where
  fresh = CoercionId <$> fresh

instance (Applicative m, Fresh m a) => Fresh m (EqProp a) where
  fresh = (:~:) <$> fresh <*> fresh

freshes
  :: forall t m
  .  (Generic t, ADTRecord t, Constraints t (Fresh m), Applicative m)
  => m t
freshes = createA' (For :: For (Fresh m)) fresh

data Ctx = Ctx
  { varCtx :: [(VarId, DCId)]
  , cVarCtx :: [(CVarId, EqProp DCId)]
  } deriving (Eq, Ord, Show)

emptyCtx :: Ctx
emptyCtx = Ctx [] []

data Ctx' = Ctx' [CVarId]
  deriving (Eq, Ord, Show)

cctx :: Ctx -> Ctx'
cctx ctx = Ctx' [c | (c, _) <- cVarCtx ctx]

pickVar :: MonadSoup m => Ctx -> m (VarId, DCId)
pickVar ctx = pick (varCtx ctx)

insertVar :: VarId -> DCId -> Ctx -> Ctx
insertVar x ty ctx = ctx { varCtx = (x, ty) : varCtx ctx }

insertCVar :: CVarId -> EqProp DCId -> Ctx -> Ctx
insertCVar c phi ctx = ctx { cVarCtx = (c, phi) : cVarCtx ctx }

alternate3 :: MonadSoup m => [a -> b -> c -> m d] -> a -> b -> c -> m d
alternate3 fs a b c = pick fs >>= \f -> f a b c

typeCheck :: MonadSoup m => Ctx -> DCId -> DCId -> m [K]
typeCheck = alternate3
  [ tcStar
  , tcVar
  , tcPi
  , tcAbs
  , tcApp
  ]

tcStar, tcVar, tcPi, tcAbs, tcApp, tcConv, tcCoPi,
  tcCoAbs, tcCoApp
  :: MonadSoup m => Ctx -> DCId -> DCId -> m [K]

tcStar _ctx t tyT = do
  return
    [ kEqDC t (RHSHead Star)
    , kEqDC tyT (RHSHead Star)
    ]

tcVar ctx t tyT = do
  (x, ty) <- pickVar ctx
  return
    [ kEqDC t (RHSHead (Var x))
    , kEqDC tyT (RHSId ty)
    ]

tcPi ctx t tyStar = do
  rel <- pick [Rel, Irr]
  (x, tyA, tyB) <- freshes
  let ctx' = insertVar x tyA ctx
  return
    [ kEqDC t (RHSHead (Pi rel x tyA tyB))
    , kEqDC tyStar (RHSHead Star)
    , KType ctx' tyB tyStar
    , KWF ctx'
    , K_ (KType ctx tyA tyStar)
    ]

tcAbs ctx t tyT = do
  rel <- pick [Rel, Irr]
  (x, tyA, b, tyB, tyStar) <- freshes
  let ctx' = insertVar x tyA ctx
  return
    [ kEqDC t (RHSHead (Abs rel x tyA b))
    , kEqDC tyT (RHSHead (Pi rel x tyA tyB))
    , KType ctx' b tyB
    , KWF ctx'
    , KRel rel x b
    , K_ (kEqDC tyStar (RHSHead Star))
    , K_ (KType ctx tyA tyStar)
    ]

tcApp ctx t tyT = do
  rel <- pick [Rel, Irr]
  (b, a, x, tyA, ty', tyB) <- freshes
  return
    [ kEqDC t   (RHSHead (App b a rel))
    , kEqDC tyB (RHSHead (Pi rel x tyA ty'))
    , kEqDC tyT (RHSSub x a ty')
    , KType ctx b tyB
    , KType ctx a tyA
    ]

tcConv ctx t tyB = do
  (a, g, tyA, tyStar) <- freshes
  return
    [ kEqDC t (RHSHead (Coerce a g))
    , kEqDC tyStar (RHSHead Star)
    , KType ctx tyB tyStar
    , KType ctx a tyA
    , KTypeC ctx (cctx ctx) g (tyA :~: tyB)
    ]

tcCoPi ctx t tyStar = do
  (c, phi, tyB) <- freshes
  let ctx' = insertCVar c phi ctx
  return
    [ kEqDC t (RHSHead (CoPi c phi tyB))
    , kEqDC tyStar (RHSHead Star)
    , KType ctx' tyB tyStar
    , KWF ctx'
    , K_ (KOK ctx phi)
    ]

tcCoAbs ctx t tyT = do
  (c, phi, b, tyB) <- freshes
  let ctx' = insertCVar c phi ctx
  return
    [ kEqDC t   (RHSHead (CoAbs c phi b))
    , kEqDC tyT (RHSHead (CoPi c phi tyB))
    , KType ctx' b tyB
    , KWF ctx'
    , K_ (KOK ctx phi)
    ]

tcCoApp ctx t tyT = do
  (a, g, c, phi, tyB, ty') <- freshes
  return
    [ kEqDC t   (RHSHead (CoApp a g))
    , kEqDC tyT (RHSSubC c g tyB)
    , kEqDC ty' (RHSHead (CoPi c phi tyB))
    , KType ctx a ty'
    , KTypeC ctx (cctx ctx) g phi
    ]

initK :: MonadSoup m => m ([K], DCId, DCId)
initK = do
  (t, ty) <- freshes
  return
    ([KType emptyCtx t ty], t, ty)

--

data S h = S
  { counter :: !Integer
  , constraints :: h
  } deriving Show

type ForkF = ExceptT () []

newtype M h a = M { unM :: M' h a }
  deriving (Functor, Applicative, Monad)

type M' h = StateT (S h) ForkF

instance Fresh (M h) Integer where
  fresh = M . state $ \s ->
    let i = counter s in (i, s {counter = i+1})

instance MonadSoup (M h) where
  pick = M . lift . lift

runM :: KStore h => M h [K] -> S h -> ForkF (S h)
runM = execStateT . unM . (>>= andKs)

class KStore h where
  initStore :: h
  andK :: K -> M h ()
  reduce :: M h ()
  extractKType :: (Ctx -> DCId -> DCId -> M h a) -> M h a

  andKs :: KStore h => [K] -> M h ()
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

type HSimple = [K]

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

isKType :: K -> Bool
isKType (KType{}) = True
isKType _ = False

data H1 = H1
  { eqns :: Map DCId Alias
  , ks1 :: [K]
  , vUF :: UnionFind VarId
  , cUF :: UnionFind CVarId
  } deriving Show

mergeH1Var :: VarId -> VarId -> M' H1 ()
mergeH1Var v1 v2 =
  l @"ks" . l @"vUF" %= mergeUF v1 v2

equalH1Var :: VarId -> VarId -> M' H1 Bool
equalH1Var v1 v2 = do
  s <- get
  return (equalUF v1 v2 (s ^. l @"ks" . l @"vUF"))

data Alias
  = Alias DCId
  | Head (DCore_ Soup)
  deriving (Eq, Show)

ksH1 :: Lens' (S H1) [K]
ksH1 = l @"ks" . l @"ks"

eqnsH1 :: Lens' (S H1) (Map DCId Alias)
eqnsH1 = l @"ks" . l @"eqns"

instance KStore H1 where
  initStore = H1 Map.empty [] emptyUF emptyUF
  andK k = M $ ksH1 %= (k :)
  reduce = reduceH1
  extractKType r = M $ do
    s <- get
    (go, ks) <- (lift . lift)
      [ (r ctx t ty, ks)
      | (KType ctx t ty, ks) <- focus (s ^. ksH1) ]
    ksH1 .= ks
    unM go

reduceH1 :: M H1 ()
reduceH1 = M $ do
  s <- get
  reduceH1' (s ^. ksH1)

reduceH1' :: [K] -> M' H1 ()
reduceH1' ks = do
  ks <- traverseCollectRetry reduceH1Atom ks
  ksH1 .= ks

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
reduceH1Atom ret (KEqDC t rhs) = reduceH1EqDC t rhs >> ret [] False

reduceH1EqDC :: DCId -> RHS -> M' H1 ()
reduceH1EqDC t (RHSId u) = reduceH1EqDCId t u

reduceH1EqDCId :: DCId -> DCId -> M' H1 ()
reduceH1EqDCId t u = do
  t_ <- lookupH1V t
  u_ <- lookupH1V u
  case (t_, u_) of
    (Left t, Left u) | t == u -> return ()
    (Left t, Right (u, f)) ->
      alias t u f
    (Right (t, e), Left u) ->
      alias u t e
    (Right (t, e), Right (u, f)) | t == u -> return ()
    (Right (t, e), Right (u, f)) -> do
      reduceH1EqHead e f
      unsafeAlias u t

alias :: DCId -> DCId -> DCore_ Soup -> M' H1 ()
alias t u e = do
  occursCheck' t e
  unsafeAlias t u

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

unsafeAlias :: DCId -> DCId -> M' H1 ()
unsafeAlias t u = eqnsH1 %= Map.insert t (Alias u)

lookupH1V :: DCId -> M' H1 (Either DCId (DCId, DCore_ Soup))
lookupH1V t = do
  s <- get
  case Map.lookup t (s ^. eqnsH1) of
    Just (Alias v) -> lookupH1V v
    Nothing -> return (Left t)
    Just (Head e) -> return (Right (t, e))

reduceH1EqHead
  :: DCore_ Soup -> DCore_ Soup -> M' H1 ()
reduceH1EqHead e1 e2 = case (e1, e2) of
  (Star, Star) -> return ()
  (Star, _) -> empty

  (Var v1, Var v2) -> do
        eq <- equalH1Var v1 v2
        if eq then
          return ()
        else
          empty
  (Var{}, _) -> empty

  (Abs rel1 v1 tyA1 b1, Abs rel2 v2 tyA2 b2)
    | rel1 == rel2 -> do
        mergeH1Var v1 v2
        reduceH1EqDCId tyA1 tyA2
        reduceH1EqDCId b1 b2
  (Abs{}, _) -> empty

  (Pi rel1 v1 tyA1 tyB1, Pi rel2 v2 tyA2 tyB2)
    | rel1 == rel2 -> do
        mergeH1Var v1 v2
        reduceH1EqDCId tyA1 tyA2
        reduceH1EqDCId tyB1 tyB2
  (Pi{}, _) -> empty

  (App b1 a1 rel1, App b2 a2 rel2)
    | rel1 == rel2 -> do
        reduceH1EqDCId b1 b2
        reduceH1EqDCId a1 a2

  (App{}, _) -> empty

focus :: [a] -> [(a, [a])]
focus = focus' []
  where
    focus' _ [] = []
    focus' aux (a : as) = (a, aux) : focus' (a : aux) as

tree' :: Cofree (Elide ForkF) (S HSimple)
tree' = takeDepth 2 tree

size :: Foldable f => Cofree f a -> Integer
size = getSum . size'
  where size' (_ :< f) = 1 + foldMap size' f

class L (n :: Symbol) s a | n s -> a where
  l :: Lens' s a

instance L "ks" (S h) h where
  l f s = fmap (\h -> s { constraints = h }) (f (constraints s))

instance L "ks" H1 [K] where
  l f h = fmap (\ks -> h { ks1 = ks }) (f (ks1 h))

instance L "eqns" H1 (Map DCId Alias) where
  l f h = fmap (\eqns -> h { eqns = eqns }) (f (eqns h))

instance L "vUF" H1 (UnionFind VarId) where
  l f h = fmap (\vUF -> h { vUF = vUF }) (f (vUF h))
