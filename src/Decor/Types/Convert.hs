{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Decor.Types.Convert where

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

