{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.Aeson
import Data.Aeson.Types

import Decor.Soup
import Decor.Soup.Simple
import Decor.Types
import Decor.Utils

main = print (toJSON treeH1)

deriving instance Generic (Free f a)

deriving instance ToJSONKey DCId

instance ToJSON (DCore_ Soup) where
  toJSON = toJSON . showDCoreSoup

instance (ToJSON a, ToJSON (f (Free f a))) => ToJSON (Free f a) where
  toJSON = genericToJSON defaultOptions{sumEncoding=UntaggedValue}

instance (ToJSON s, ToJSON a) => ToJSON (ChoiceF s a) where
  toJSON = genericToJSON defaultOptions{sumEncoding=ObjectWithSingleField}

instance ToJSON h => ToJSON (S h) where
  toJSON s = case toJSON (constraints s) of
    Object o -> Object $ o `mappend` [("counter", toJSON (counter s))]

instance ToJSON H1

instance ToJSON K1 where
  toJSON = toJSON . showK1

showDCoreSoup :: DCore_ Soup -> String
showDCoreSoup t = case t of
  Star -> "*"
  Var (DeBruijnV x) -> "|" ++ show x
  App t u rel -> show t ++ " " ++ show u ++ sRel rel
  Pi rel () u v -> "Π" ++ sRel rel ++ " " ++ show u ++ " -> " ++ show v
  Abs rel () u v -> "λ" ++ sRel rel ++ " " ++ show u ++ " . " ++ show v

sRel :: Rel -> String
sRel Rel = "+"
sRel Irr = "-"

showK1 :: K1 -> String
showK1 = undefined
