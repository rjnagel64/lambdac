
module Experiments.Inline where

import CPS.IR

-- An implementation of Dybvig's Inlining Algorithm:
-- [Fast and Effective Inlining Procedure], Dybvig 2004.

import qualified Data.IntMap as IMap
import Data.IntMap (IntMap)


newtype VarLoc = VarLoc Int
newtype ExpLoc = ExpLoc Int
newtype ContextLoc = ContextLoc Int

-- "Inlining variables": auxiliary structures computed during inlining.
data IVar
  = IVar {
    varName :: TmVar
  , varOpnd :: Maybe Operand
  , varFlags :: VarFlags
  , varLoc :: VarLoc
  }

data VarFlags = VarFlags { vfRef :: Bool, vfAssign :: Bool }

data Operand
  = Operand {
    opndExp :: Term ()
  , opndEnv :: Env
  , opndLoc :: ExpLoc
  }

-- | The context describes where/for what purpose an expression is being
-- evaluated.
data Context
  -- Not useful: requires "truthy" conditional semantics
  = Test
  -- Not (yet) useful: requires impure operations
  | Effect
  -- Evaluate an expression for its value
  | Value
  -- Evaluate something in operator position, and evaluate its result in another context
  | Applied Operand Context ContextLoc

newtype Env = Env { runEnv :: IVar -> IVar }

data Store
  = Store {
    storeVars :: IntMap VarFlags
  , storeContexts :: IntMap ContextFlags
  , storeExps :: IntMap (Maybe (Term ()))
  }

newtype Cont = Cont { runCont :: Term () -> Store -> Term () }


-- Hmm. One really big problem with my current setup for CPS.IR is that I can
-- only have values in very few places. This means that I'm going to need to
-- insert lots of 'LetValK' expressions in ad-hoc ways.
--
-- As with the hybrid-cps algorithm, I'm beginning to think that it would be
-- better to not use ANF for CPS, and instead "flatten" values in a later
-- stage.
--
-- I don't think I can implement this right now, unfortunately.
inline : Term () -> Context -> Env -> Cont -> Store -> Term ()
inline e g r k s = e -- Can't implement right now, just residualize the whole program.
