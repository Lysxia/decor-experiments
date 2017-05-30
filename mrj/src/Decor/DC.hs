-- | Type checker for DC

module Decor.DC where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import Prelude hiding (lookup)

import Decor.Types.DC

type Ctx = Map VarId DC

lookup :: VarId -> Ctx -> Maybe DC
lookup = Map.lookup

insert :: VarId -> DC -> Ctx -> Ctx
insert = Map.insert

insertC :: CVarId -> EqProp DC -> Ctx -> Ctx
insertC = undefined

-- | Check and infer the type of DC.
typeCheck :: Ctx -> DC -> Maybe DC
typeCheck _ctx Star = Just Star
typeCheck ctx (Var v) = lookup v ctx
typeCheck ctx (Pi _rel v tyA tyB) = do
  -- Star <- typeCheck ctx tyA Star
  Star <- typeCheck (insert v tyA ctx) tyB
  return Star
typeCheck ctx (Abs rel v tyA b) = do
  guard (relevanceCheck rel v b)
  -- Star <- typeCheck ctx tyA
  tyB <- typeCheck (insert v tyA ctx) b
  return (Pi rel v tyA tyB)
typeCheck ctx (App b a rel) = do
  Pi rel' x tyA' tyB <- typeCheck ctx b
  guard (rel' == rel)
  tyA <- typeCheck ctx a
  guard (tyA == tyA')
  return (subst x tyA tyB)
typeCheck ctx (Coerce a g) = do
  tyA <- typeCheck ctx a
  tyA' :~: tyB <- typeCheckC ctx (cctx ctx) g
  guard (tyA == tyA')
  Star <- typeCheck ctx tyB
  return tyB
typeCheck ctx (CoPi c phi tyB) = do
  guard (ok ctx phi)
  Star <- typeCheck (insertC c phi ctx) tyB
  return Star
typeCheck ctx (CoAbs c phi b) = do
  guard (ok ctx phi)
  tyB <- typeCheck (insertC c phi ctx) b
  return (CoPi c phi tyB)
typeCheck ctx (CoApp a g) = do
  CoPi c phi tyB <- typeCheck ctx a
  phi' <- typeCheckC ctx (cctx ctx) g
  guard (phi == phi')
  return (subst' c g tyB)

wf :: Ctx -> Bool
wf ctx = undefined

ok :: Ctx -> EqProp DC -> Bool
ok = undefined

cctx :: Ctx -> ctx
cctx = undefined

relevanceCheck :: Rel -> VarId -> DC -> Bool
relevanceCheck = undefined

subst :: VarId -> DC -> DC -> DC
subst v a = s
  where
    s Star = Star
    s (Var v') | v == v' = a
    s t@(Var _) = t
    s (Pi rel x tyA tyB)
      = Pi rel x (s tyA) ((if v == x then id else s) tyB)
    s (Abs rel x tyA b)
      = Abs rel x (s tyA) ((if v == x then id else s) b)
    s (App b d rel) = App (s b) (s d) rel
    s (CoPi c phi tyB) = CoPi c (substPhi v a phi) (s tyB)
    s (CoAbs c phi b) = CoAbs c (substPhi v a phi) (s b)
    s (CoApp b g) = CoApp (s b) (substC v a g)
    s (Coerce b g) = Coerce (s b) (substC v a g)

substPhi :: VarId -> DC -> EqProp DC -> EqProp DC
substPhi v a (tyA :~: tyB) = subst v a tyA :~: subst v a tyB

substC :: VarId -> DC -> Coercion -> Coercion
substC v a = s
  where
    s :: Coercion -> Coercion
    s g@(CVar _) = g
    s (CRefl b) = CRefl (subst v a b)
    s (CRefl' phi g) = CRefl' (substPhi v a phi) (s g)
    s (CSym g) = CSym (s g)
    s (CSeq g1 g2) = CSeq (s g1) (s g2)
    s (CRed b d) = CRed (subst v a b) (subst v a d)
    s (CPi rel x gA gB) = CPi rel x (s gA) ((if v == x then id else s) gB)
    s (CAbs rel x gA gb) = CAbs rel x (s gA) ((if v == x then id else s) gb)
    s (CApp gb ga rel) = CApp (s gb) (s ga) rel


typeCheckC :: Ctx -> ctx -> Coercion -> Maybe (EqProp DC)
typeCheckC = undefined

subst' :: CVarId -> Coercion -> DC -> DC
subst' = undefined
