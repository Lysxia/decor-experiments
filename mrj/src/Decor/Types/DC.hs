{-# LANGUAGE DeriveGeneric #-}

module Decor.Types.DC where

import GHC.Generics

-- | Relevance
data Rel = Rel | Irr
  deriving (Eq, Ord, Show)

data DC
  = Star
  | Var VarId
  | Fun FunId

  | Pi  Rel VarId DC DC
  | Abs Rel VarId DC DC
  | App DC DC Rel

  | CoPi  CVarId (EqProp DC) DC
  | CoAbs CVarId (EqProp DC) DC
  | CoApp DC Coercion

  | Coerce DC Coercion

  deriving (Eq, Ord, Show, Generic)

data Coercion
  = CVar CVarId
  | CRefl DC
  | CRefl' (EqProp DC) Coercion
  | CSym Coercion
  | CSeq Coercion Coercion
  | CRed DC DC
  | CPi  Rel VarId Coercion Coercion
  | CAbs Rel VarId Coercion Coercion
  | CApp Coercion Coercion Rel
  | CCoPi  CVarId Coercion Coercion
  | CCoAbs CVarId Coercion Coercion Coercion
  | CCoApp Coercion Coercion Coercion
  deriving (Eq, Ord, Show, Generic)

newtype VarId = VarId Integer
  deriving (Eq, Ord, Show)

newtype CVarId = CVarId Integer
  deriving (Eq, Ord, Show)

newtype FunId = FunId Integer
  deriving (Eq, Ord, Show)

data EqProp a = (:~:) a a
  deriving (Eq, Ord, Show)

