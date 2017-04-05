-- | Types for a dependently-typed calculus with coercions.

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Decor.Types where

import GHC.Exts (Constraint)
import GHC.Generics (Generic)

type family VarT  p
type family BindVarT p
type family FunT  p
type family CVarT p
type family BindCVarT p
type family RelT p
type family DCore p
type family Coercion p

-- | Relevance
data Rel = Rel | Irr
  deriving (Eq, Ord, Show)

data DCore_ p

  = Star
  | Var (VarT p)
  | Fun (FunT p)

  | Abs (RelT p) (BindVarT p) (DCore p) (DCore p)
  | Pi (RelT p) (BindVarT p) (DCore p) (DCore p)
  | App (DCore p) (DCore p) (RelT p)

  | CoAbs (BindCVarT p) (EqProp (DCore p)) (DCore p)
  | CoPi (BindCVarT p) (EqProp (DCore p)) (DCore p)
  | CoApp (DCore p) (Coercion p)

  | Coerce (DCore p) (Coercion p)

  deriving Generic

type Syntax (c :: * -> Constraint) p =
  ( c (VarT p)
  , c (FunT p)
  , c (RelT p)
  , c (BindVarT p)
  , c (BindCVarT p)
  , c (CVarT p)
  , c (DCore p)
  , c (Coercion p)
  )

deriving instance
  Syntax Eq p => Eq (DCore_ p)

deriving instance
  Syntax Ord p => Ord (DCore_ p)

deriving instance
  Syntax Show p => Show (DCore_ p)

data Coercion_ p
  = CVar (CVarT p)
  | CRefl (DCore p)
  | CRefl' (DCore p) (DCore p) (Coercion p)
  | CSym (Coercion p)
  | CSeq (Coercion p) (Coercion p)
  | CRed (DCore p) (DCore p)
  | CAbs (RelT p) (BindVarT p) (Coercion p) (Coercion p)
  | CApp (Coercion p) (Coercion p) Rel
  | CPi (RelT p) (BindVarT p) (Coercion p) (Coercion p)
  | CCoAbs (BindCVarT p) (Coercion p) (Coercion p) (Coercion p)
  | CCoPi (BindCVarT p) (Coercion p) (Coercion p)
  | CCoApp (Coercion p) (Coercion p) (Coercion p)
  deriving Generic

deriving instance
  Syntax Show p => Show (Coercion_ p)

data EqProp a = (:~:) a a
  deriving (Eq, Ord, Show)

newtype VarId = VarId Integer
  deriving (Eq, Ord, Show)

newtype CVarId = CVarId Integer
  deriving (Eq, Ord, Show)

newtype FunId = FunId Integer
  deriving (Eq, Ord, Show)

newtype L = L String

instance Show L where
  show (L s) = s
