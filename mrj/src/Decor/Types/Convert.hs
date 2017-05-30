{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Decor.Types.Convert where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Data.List (elemIndex)
import Text.Read (readEither)

import Decor.Types

class (RelT p ~ Rel, RelT p' ~ Rel, Applicative m) => Converter p p' m | m -> p p' where
  convertVar :: VarT p -> m (VarT p')
  convertFun :: FunT p -> m (FunT p')
  bindV :: BindVarT p -> (BindVarT p' -> (forall a. m a -> m a) -> m b) -> m b
  convert_ :: DCore p -> m (DCore p')

convertDCore :: forall p p' m. Converter p p' m => DCore_ p -> m (DCore_ p')
convertDCore t = case t of
  Star -> pure Star
  Var v -> Var <$> convertVar @p @p' v
  Fun f -> Fun <$> convertFun @p @p' f
  Pi rel v tyA tyB ->
    bindV @p @p' v $ \v' under -> Pi rel v' <$> convert_ tyA <*> under (convert_ tyB)
  Abs rel v tyA b ->
    bindV @p @p' v $ \v' under -> Abs rel v' <$> convert_ tyA <*> under (convert_ b)
  App b a rel -> App <$> convert_ b <*> convert_ a <*> pure rel

newtype PartialToTree a = PartialToTree
  { unPartialToTree :: ReaderT [String] (Either String) a }
  deriving (Functor, Applicative)

partialToTree :: ([String] -> Either String a) -> PartialToTree a
partialToTree = PartialToTree . ReaderT

runPartialToTree :: PartialToTree a -> [String] -> Either String a
runPartialToTree = runReaderT . unPartialToTree

instance Converter Partial Tree PartialToTree where
  convertVar v = partialToTree $ \ctx ->
    case elemIndex v ctx of
      Nothing -> Left $ "Unbound variable " ++ show v
      Just i -> pure (DeBruijnV (fromIntegral i))
  convertFun f = partialToTree $ \_ -> readEither f
  bindV v k = k () $ \f -> partialToTree $ \ctx -> runPartialToTree f (v : ctx)
  convert_ t = partialToTree $ \ctx ->
    note "Still partial" t >>= \t -> runPartialToTree (convertDCore t) ctx

convertPartialToTree :: DCore Partial -> Either String (DCore Tree)
convertPartialToTree t = runPartialToTree (convert_ t) []

defaultNames :: [String]
defaultNames = liftA2 (flip (:)) ("" : fmap pure ['0' .. '9'] ++ defaultNames) ['a' .. 'z']

newtype TreeToPartial a = TreeToPartial
  { unTreeToPartial :: ReaderT [String] (State [String]) a }
  deriving (Functor, Applicative)

treeToPartial :: ([String] -> State [String] a) -> TreeToPartial a
treeToPartial = TreeToPartial . ReaderT

runTreeToPartial :: TreeToPartial a -> [String] -> State [String] a
runTreeToPartial = runReaderT . unTreeToPartial

instance Converter Tree Partial TreeToPartial where
  convertVar (DeBruijnV v) = treeToPartial $ \ctx -> case drop (fromIntegral v) ctx of
    [] -> error $ "Out of bound de Bruijn index " ++ show v
    v : _ -> return v
  convertFun f = pure (show f)
  bindV () k = treeToPartial $ \ctx -> do
    v' : names <- get
    put names
    let h = k v' $ \m -> treeToPartial $ \ctx -> runTreeToPartial m (v' : ctx)
    runTreeToPartial h ctx
  convert_ t = fmap Just (convertDCore t)

convertTreeToPartial' :: [String] -> DCore Tree -> DCore Partial
convertTreeToPartial' names t = evalState (runTreeToPartial (convert_ t) []) names

convertTreeToPartial :: DCore Tree -> DCore Partial
convertTreeToPartial = convertTreeToPartial' defaultNames

note :: String -> Maybe a -> Either String a
note s Nothing = Left s
note _ (Just e) = Right e
