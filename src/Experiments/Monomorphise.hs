
module Experiments.Monomorphise where

-- Experiment: deal with polymorphism and CPS by just eliminating the
-- polymorphism first.

-- Basically, translate System F to STLC?

-- Monomorphising prenex polymorphism is super easy.
-- Monomorphising rank-n polymorphism: harder?
-- Monomorphising HKTs: I think this is possible
-- Monomorphising impredicative types: I dare to believe
-- Monomorphising polymorphic recursion: ha, no.
--
-- ... Okay, Andreas Rossberg says no. Aw. (first-class universal or
-- existential quantifiers cannot completely be eliminated)
-- I guess I have to stick to prenex polymorphism.
-- (The origin of this statement is apparently on Lambda the Ultimate, however,
-- the site is down and will likely continue to be unless fixed)
-- (Someone else did quote the statement as part of their "topics requiring
-- investigation to understand" list: https://steshaw.org/notes/todo.html)

import Control.Monad.Reader
import Control.Monad.Writer

data Var = Var String
data TVar = TVar String

data BaseType
  = BaseUnit
  | BaseBool
  | BaseInt

-- System F.
data Poly
  = PolyVarOcc Var
  | PolyLam Var PolyType Poly
  | PolyApp Poly Poly
  | PolyLet Var PolyType Poly Poly
  | PolyAbst TVar Poly -- \ @a. e
  | PolyInst Poly PolyType -- e @t

data PolyType
  = PolyTVarOcc TVar
  | PolyAll TVar PolyType
  | PolyBase BaseType
  | PolyArr PolyType PolyType


-- STLC
data Mono
  = MonoVarOcc Var
  | MonoLam Var MonoType Mono
  | MonoApp Mono Mono
  | MonoLet Var MonoType Mono Mono

data MonoType
  = MonoBase BaseType
  | MonoArr MonoType MonoType


data Env
  = Env {
    envPoly :: Map Var (TVar, Poly)
  , envMono :: Map (Var, PolyType) (Var, Mono)
  , envAppCtx :: AppCtx
  }

data AppCtx
  = Hole
  | AppTm Poly
  | AppTy PolyType

data MonoDefs = MonoDefs [(Var, MonoType, Mono)]

newtype M a = M { runM :: ReaderT Env (Writer MonoDefs) a }

-- Annotate each let-binding with its (monomorphic?) instantiations
-- instantiations :: Poly -> Map

-- monomorphise :: Poly -> M Mono
-- monomorphise (PolyLet x s e1 e2) = _
-- monomorphise (PolyAbst aa e) = _

data Prenex
  = PrenexVarOcc Var
  | PrenexAbst Var PrenexType Prenex Prenex -- let x : s = e1 in e2
  | PrenexInst Var Var [MonoType] Prenex -- let x = y @tt+ in e. No impredicative inst?
  | PrenexLam Var MonoType Prenex
  | PrenexApp Prenex Prenex
  | PrenexLet Var MonoType Prenex Prenex -- let x : t = e1 in e2

data PrenexType
  = Prenex [TyVar] MonoType

-- Prenex polymorphism: split types into monotypes and polytypes.
-- Easy to monomorphise.
monomorphisePrenex :: Prenex -> M Mono
-- Turn this into a let-binding with a monomorphised version of the body of `y`
monomorphisePrenex (PrenexInst x y ts e) = do
  (Prenex as t, def) <- lookupPoly y
  (t', def') <- instantiate t def as ts
  e' <- monomorphisePrenex e -- Extend scope with x : t'?
  pure (MonoLet x t' def' e') 
