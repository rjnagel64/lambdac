{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeFamilies, FlexibleInstances #-}

module Experiments.STLC where

-- PHOAS implementation of continuation passing style for well-typed STLC.
-- Based on [Parametric Higher-Order Abstract Syntax for Mechanized Semantics]

-- See https://stackoverflow.com/questions/19415621/parsing-for-phoas-expressions
-- for conversion of raw names to PHOAS

-- TODO: Evaluators for source (easy) and CPS (harder)
-- New RuntimeValue type used to instantiate CPS variable type?

import qualified Data.Map as Map
import Data.Map (Map)

data Type = TyBool | TyArr Type Type

-- TODO: Add source-level products (since I have core-level products)
-- TODO: Add 'if'. (TermK constructor, probably)
-- TODO: Add sum types (Like 'if', but a bit more complicated.)
data Term (v :: Type -> *) :: Type -> * where
  -- I could also add TmGlobal String for free variable references
  -- PHOAS apparently also plays nicely with effectul interpreter
  TmVarOcc :: v a -> Term v a
  TmApp :: Term v ('TyArr a b) -> Term v a -> Term v b
  TmLam :: String -> (v a -> Term v b) -> Term v ('TyArr a b)
  TmTrue :: Term v 'TyBool
  TmFalse :: Term v 'TyBool


-- τ = bool | τ -> 0 | τ × τ
data TypeK = BoolK | ContK TypeK | ProdK TypeK TypeK

-- Terms do not return directly, but they are still indexed by the type
-- expected by their top-level continuation.
-- The parameters/indices used by the binding constructs are quite subtle.
data TermK (v :: TypeK -> *) (a :: TypeK) :: * where
  HaltK :: v a -> TermK v a
  -- The return type here is polymorphic because we apply @x -> 0@ to @x@, not
  -- returning.
  JumpK :: v ('ContK x) -> v x -> TermK v a
  LetK :: PrimK v a x -> String -> (v x -> TermK v a) -> TermK v a

-- Primitives are indexed by the type of their value.
-- Primitives are parametrized by the sort of variables used, as well as the
-- argument type expected by the "top-level continuation".
-- I'm not really clear on what that means, but it's important and kind of
-- subtle.
data PrimK (v :: TypeK -> *) (a :: TypeK) :: TypeK -> * where
  VarK :: v x -> PrimK v a x
  TrueK :: PrimK v a 'BoolK
  FalseK :: PrimK v a 'BoolK
  FunK :: String -> (v x -> TermK v a) -> PrimK v a ('ContK x)
  PairK :: v x -> v y -> PrimK v a ('ProdK x y)
  FstK :: v (ProdK x y) -> PrimK v a x
  SndK :: v (ProdK x y) -> PrimK v a y


-- Pretty-printing
data Name :: TypeK -> * where
  Name :: String -> Int -> Name a

instance Show (Name a) where
  show (Name x i) = x ++ show i

type Scope = Map String Int

emptyScope :: Scope
emptyScope = Map.empty

pprintTerm :: Scope -> TermK Name a -> String
pprintTerm sc (HaltK x) = "halt " ++ show x
pprintTerm sc (LetK p x' f) =
  "let " ++ show x ++ " = " ++ pprintPrim sc p ++ " in " ++ pprintTerm sc' (f x)
  where (x, sc') = freshName x' sc
pprintTerm sc (JumpK x y) = show x ++ " " ++ show y

pprintPrim :: Scope -> PrimK Name a b -> String
pprintPrim sc (VarK x) = show x
pprintPrim sc TrueK = "true"
pprintPrim sc FalseK = "false"
pprintPrim sc (PairK x y) = "<" ++ show x ++ "," ++ show y ++ ">"
pprintPrim sc (FstK x) = "fst " ++ show x
pprintPrim sc (SndK x) = "snd " ++ show x
pprintPrim sc (FunK x' f) = "(λ" ++ show x ++ ". " ++ pprintTerm sc' (f x) ++ ")"
  where (x, sc') = freshName x' sc

freshName :: String -> Scope -> (Name a, Scope)
freshName x' sc = case Map.lookup x' sc of
  Nothing -> (Name x' 0, Map.insert x' 1 sc)
  Just i -> (Name x' i, Map.insert x' (i+1) sc)


-- CPS transform

type family CpsType (a :: Type) :: TypeK where
  -- K[bool] = bool
  CpsType 'TyBool = 'BoolK
  -- K[a -> b] = <a, K[b] -> 0> -> 0
  CpsType ('TyArr a b) = 'ContK ('ProdK (CpsType a) ('ContK (CpsType b)))
  -- K[a × b] = K[a] × K[b]

-- No anonymous composition. Use newtype wrapper
newtype CpsVar v a = CpsVar { getCpsVar :: v (CpsType a) }

cpsTerm :: Term (CpsVar v) a -> TermK v (CpsType a)
cpsTerm (TmVarOcc x) = HaltK (getCpsVar x)
cpsTerm TmTrue = LetK TrueK "x" (\x -> HaltK x)
cpsTerm TmFalse = LetK FalseK "x" (\x -> HaltK x)
cpsTerm (TmLam _x' f) =
  LetK (FunK "p" $ \p ->
    LetK (FstK p) "x" $ \x ->
      LetK (SndK p) "k" $ \k ->
        letTerm (cpsTerm (f (CpsVar x))) $ \r -> JumpK k r)
    "f" (\f -> HaltK f)
cpsTerm (TmApp e1 e2) =
  letTerm (cpsTerm e1) $ \f ->
    letTerm (cpsTerm e2) $ \x ->
      LetK (FunK "r" (\r -> HaltK r)) "k" $ \k ->
        LetK (PairK x k) "p" $ \p ->
          JumpK f p

-- Desugar @let e in x. e'@ into @let p in x. e'@
letTerm :: TermK v a -> (v a -> TermK v b) -> TermK v b
letTerm (HaltK x) e' = e' x
-- The continuation is discarded here because a jump never returns to e'.
letTerm (JumpK x y) e' = JumpK x y
letTerm (LetK p x' e) e' = LetK (letPrim p e') x' (\x -> letTerm (e x) e')

letPrim :: PrimK v a c -> (v a -> TermK v b) -> PrimK v b c
letPrim (FunK x' f) e' = FunK x' (\x -> letTerm (f x) e')
letPrim TrueK e' = TrueK
letPrim FalseK e' = FalseK
letPrim (PairK x y) e' = PairK x y
letPrim (FstK x) e' = FstK x
letPrim (SndK x) e' = SndK x



data Value :: Type -> * where
  VTrue :: Value 'TyBool
  VFalse :: Value 'TyBool
  -- Can't stringify.
  -- Maybe I need to make this parametric as well?
  -- Then I would need a VVarOcc, which I don't like.
  -- eval :: Term (Value v) a -> Value v a
  -- Stringifying isn't that important? If it's a language runtime, useful
  -- programs won't evaluate to functions.
  VFun :: (Value a -> Term Value b) -> Value ('TyArr a b)

eval :: Term Value a -> Value a
eval (TmVarOcc v) = v
eval (TmApp e1 e2) = case (eval e1, eval e2) of
  (VFun f, v) -> eval (f v)
eval (TmLam x f) = VFun f
eval TmTrue = VTrue
eval TmFalse = VFalse
