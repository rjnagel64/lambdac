
module Experiments.Inline where

-- An implementation of Dybvig's Inlining Algorithm:
-- [Fast and Effective Inlining Procedure], Dybvig 2004.

-- One major problem is that this algorithm is designed for a direct-style IR.
-- My CPS.IR and all subsequent phases are in ANF instead.
-- The places where a value/an expression can appear are quite limited, so it's
-- likely that I would need to insert many LetValK constructors in an ad-hoc
-- manner, to say nothing of the fact that I need to derive rules for, say,
-- 'let x = fst y in e'.
--
-- This file will be a mostly-faithful rendition of the lisp-like language used
-- in the paper, but I will have to revise things dramatically to implement it
-- for real.

import qualified Data.IntMap as IM
import Data.IntMap (IntMap)
import qualified Data.Map as Map
import Data.Map (Map)

import Data.Maybe (fromMaybe)
import Data.Traversable (mapAccumL)

import Prelude hiding (sequence)


-- The language being transformed
newtype TmVar = TmVar String
  deriving (Eq, Ord)

-- TODO: Split into RawTerm (TmVar) and Term (IVar
-- preprocess :: RawTerm -> Term

data RawTerm
  = RawRef TmVar
  | RawConst Const
  | RawSeq RawTerm RawTerm
  | RawIf RawTerm RawTerm RawTerm
  | RawAssign TmVar RawTerm
  | RawCall RawTerm RawTerm
  | RawPrimRef PrimOp
  | RawLam TmVar RawTerm
  | RawLetRec [(TmVar, RawTerm)] RawTerm


data Term
  = TmRef IVar
  | TmConst Const
  | TmSeq Term Term
  | TmIf Term Term Term
  -- I don't think the lhs is a binder. it's an occurrence, maybe?
  -- Quite probably. The rule for inlining TmAssign renames 'x' with the
  -- environment. In contrast, the rule for TmLam doesn't, extending the env
  -- instead. This indicates that the variable here is an occurrence, not a
  -- binder.
  | TmAssign IVar Term
  -- if multi-argument functions, use [Term] here instead
  | TmCall Term Term
  | TmPrimRef PrimOp
  | TmLam IVar Term
  | TmLetRec [(IVar, Term)] Term

data Const = ConstInt Int | ConstTrue | ConstFalse | ConstVoid
  deriving Eq

-- Current version only supports one-argument functions and primops.
-- Extending to multi-arg primops should be straightforward.
data PrimOp = PrimInc

-- primops in lisp are uncurried. For multiple arguments, take [Const] instead of just Const
applyPrim :: PrimOp -> Const -> Const
applyPrim PrimInc (ConstInt i) = ConstInt (i+1)
applyPrim PrimInc _ = error "bad primop application"


-- hmm. this might also be responsible for computing the initial store \sigma_0.
-- (It's not yet clear whether the initial store should be completely empty, or
-- if it should be populated with VarFlags for each VarLoc. I'm leaning towards
-- the latter.)
preprocess :: RawTerm -> Term
preprocess e0 =
  let (e1, _) = addVarLoc e0 0 in
  let (e2, fvEnv) = upsweep e1 in
  let e3 = downsweep fvEnv e2 in
  e3

-- Annotate each variable binder and occurrence with a VarLoc.
addVarLoc :: RawTerm -> Int -> (Term, Int)
addVarLoc (RawRef x) i =
  let lx = VarLoc i in
  let ix = IVar x Nothing emptyVarFlags lx in
  (TmRef ix, i+1)
addVarLoc (RawConst c) i = (TmConst c, i)
addVarLoc (RawSeq e1 e2) i =
  let (e1', i') = addVarLoc e1 i in
  let (e2', i'') = addVarLoc e2 i' in
  (TmSeq e1' e2', i'')
addVarLoc (RawIf e1 e2 e3) i =
  let (e1', i1) = addVarLoc e1 i in
  let (e2', i2) = addVarLoc e2 i1 in
  let (e3', i3) = addVarLoc e3 i2 in
  (TmIf e1' e2' e3', i3)
addVarLoc (RawAssign x e) i =
  let lx = VarLoc i in
  let ix = IVar x Nothing emptyVarFlags lx in
  let (e', i') = addVarLoc e (i+1) in
  (TmAssign ix e', i')
addVarLoc (RawCall e1 e2) i =
  let (e1', i') = addVarLoc e1 i in
  let (e2', i'') = addVarLoc e2 i' in
  (TmCall e1' e2', i'')
addVarLoc (RawPrimRef p) i = (TmPrimRef p, i)
addVarLoc (RawLam x e) i =
  let lx = VarLoc i in
  let ix = IVar x Nothing emptyVarFlags lx in
  let (e', i') = addVarLoc e (i+1) in
  (TmLam ix e', i')
addVarLoc (RawLetRec xs e) i =
  let
    f i0 (x, e) =
      let lx = VarLoc i0 in
      let (e', i1) = addVarLoc e (i0+1) in
      let ix = IVar x Nothing emptyVarFlags lx in
      (i1, (ix, e'))
  in
  let (i2, xs') = mapAccumL f i xs in
  let (e', i3) = addVarLoc e i2 in
  (TmLetRec xs' e', i3)

-- Collect 'ref' and 'assign' flags for each program variable, annotating
-- binders with the collected flags.
upsweep :: Term -> (Term, Map TmVar VarFlags)
upsweep (TmRef (IVar x _ _ lx)) =
  let vf = VarFlags { vfRef = True, vfAssign = False } in
  (TmRef (IVar x Nothing vf lx), Map.singleton x vf)
upsweep (TmConst c) = (TmConst c, Map.empty)
upsweep (TmSeq e1 e2) =
  let (e1', env1) = upsweep e1 in
  let (e2', env2) = upsweep e2 in
  (TmSeq e1' e2', combine env1 env2)
upsweep (TmIf e1 e2 e3) =
  let (e1', env1) = upsweep e1 in
  let (e2', env2) = upsweep e2 in
  let (e3', env3) = upsweep e3 in
  (TmIf e1' e2' e3', combine (combine env1 env2) env3)
upsweep (TmAssign (IVar x _ _ lx) e) =
  let (e', env) = upsweep e in
  let vf = VarFlags { vfRef = False, vfAssign = True } in
  (TmAssign (IVar x Nothing vf lx) e', combine (Map.singleton x vf) env)
upsweep (TmCall e1 e2) =
  let (e1', env1) = upsweep e1 in
  let (e2', env2) = upsweep e2 in
  (TmCall e1' e2', combine env1 env2)
upsweep (TmPrimRef p) = (TmPrimRef p, Map.empty)
upsweep (TmLam (IVar x _ _ lx) e) =
  let (e', env) = upsweep e in
  (TmLam (IVar x Nothing (envVarFlags x env) lx) e', Map.delete x env)
upsweep (TmLetRec ixs e) =
  let (e', env) = upsweep e in
  let (ixs', envs) = unzip [((ixi, ei'), envi) | (ixi, ei) <- ixs, let (ei', envi) = upsweep ei] in
  let env' = foldr combine env envs in
  let ixs'' = [(IVar xi Nothing (envVarFlags xi env') lxi, ei') | (IVar xi _ _ lxi, ei') <- ixs'] in
  let env'' = foldr Map.delete env' [xi | (IVar xi _ _ _, _) <- ixs'] in
  (TmLetRec ixs'' e', env'')

combine :: Map TmVar VarFlags -> Map TmVar VarFlags -> Map TmVar VarFlags
combine env1 env2 = Map.unionWith unionVarFlags env1 env2
  where
    unionVarFlags (VarFlags ref1 assign1) (VarFlags ref2 assign2) = VarFlags (ref1 || ref2) (assign1 || assign2)

envVarFlags :: TmVar -> Map TmVar VarFlags -> VarFlags
-- If the variable is not in the map, that means that it was never referenced
-- and never assigned. (Not occurrences at all ==> no occurrences recorded in env)
envVarFlags x env = fromMaybe emptyVarFlags (Map.lookup x env)

-- Propagate 'ref' and 'assign' flags back down to variable occurrences.
downsweep :: Map TmVar VarFlags -> Term -> Term
downsweep env (TmRef (IVar x _ _ lx)) = TmRef (IVar x Nothing (env Map.! x) lx)
downsweep env (TmConst c) = TmConst c
downsweep env (TmSeq e1 e2) = TmSeq (downsweep env e1) (downsweep env e2)
downsweep env (TmIf e1 e2 e3) = TmIf (downsweep env e1) (downsweep env e2) (downsweep env e3)
downsweep env (TmAssign (IVar x _ _ lx) e) = TmAssign (IVar x Nothing (env Map.! x) lx) (downsweep env e)
downsweep env (TmCall e1 e2) = TmCall (downsweep env e1) (downsweep env e2)
downsweep env (TmPrimRef p) = TmPrimRef p
downsweep env (TmLam (IVar x op vf lx) e) = TmLam (IVar x op vf lx) (downsweep (Map.insert x vf env) e)
downsweep env (TmLetRec ixs e) =
  let binds = [(xi, vf) | (IVar xi op vf lxi, e) <- ixs] in
  let env' = foldr (uncurry Map.insert) env binds in
  let ixs' = [(ixi, downsweep env' ei) | (ixi, ei) <- ixs] in
  (TmLetRec ixs' (downsweep env' e))




-- Data structures associated with the inlining algorithm
newtype VarLoc = VarLoc Int
newtype ExpLoc = ExpLoc Int
newtype ContextLoc = ContextLoc Int

-- "Inlining variables": auxiliary structures computed during inlining.
-- Annoyingly, the algorithm also requires them to be present in the source
-- program, for the VarFlags and VarLoc.
-- However, I still feel like it would be possible/beneficial to split IVar
-- into SourceIVar and ResidualIVar, where SourceIVar cannot have the Operand,
-- but ResidualIVar might.
-- (type Env = SourceIVar -> ResidualIVar, basically?)
data IVar
  = IVar {
    varName :: TmVar
  , varOpnd :: Maybe Operand
  , varFlags :: VarFlags
  , varLoc :: VarLoc
  }

data VarFlags = VarFlags { vfRef :: Bool, vfAssign :: Bool }

emptyVarFlags :: VarFlags
emptyVarFlags = VarFlags { vfRef = False, vfAssign = False }

data Operand
  = Operand {
    opndExp :: Term
  , opndEnv :: Env
  , opndLoc :: ExpLoc
  }

-- | The context describes where/for what purpose an expression is being
-- evaluated.
data Context
  -- Evaluate an expression for whether it is truthy or falsy
  = Test
  -- Evaluate an expression for what side effects it produces
  | Effect
  -- Evaluate an expression for its value
  | Value
  -- Evaluate something in operator position, and evaluate its result in another context
  -- Generalization to multi-argument: lisps are usually uncurried, so this
  -- would probably take a [Operand] instead of just one?
  | Applied Operand Context ContextLoc

-- data AppContext = AppContext Operand Context ContextLoc

data ContextFlags = ContextFlags { cfInlined :: Bool }

-- The environment maps source-program (inlining) variables to residual-program inlining variables
newtype Env = Env [(IVar, IVar)]

emptyEnv = Env []

lookupEnv :: IVar -> Env -> IVar
lookupEnv ix@(IVar x _ _ lx) (Env xs) = go xs
  where
    go [] = error "ivar not in env" -- alternatively, return ix? The initial env (renaming) is supposed to act like the identity function, I think.
    go (iy@(IVar y _ _ ly, ix') : xs') = if x == y then ix' else go xs' -- compare by name or location? Maybe name?

extendEnv :: IVar -> IVar -> Env -> Env
extendEnv ix ix' (Env xs) = Env $ (ix, ix') : xs

data Store
  = Store {
    storeVars :: IntMap VarFlags
  , storeContexts :: IntMap ContextFlags
  , storeExps :: IntMap (Maybe Term)
  }

setVarRefFlag :: VarLoc -> Store -> Store
setVarRefFlag (VarLoc lx') (Store vars contexts exps) = Store (IM.alter f lx' vars) contexts exps
  where
    f Nothing = error "var not in store"
    f (Just vf) = Just $ vf { vfRef = True }

setVarAssignFlag :: VarLoc -> Store -> Store
setVarAssignFlag (VarLoc lx') (Store vars contexts exps) = Store (IM.alter f lx' vars) contexts exps
  where
    f Nothing = error "var not in store"
    f (Just vf) = Just $ vf { vfAssign = True }

setContextInlinedFlag :: ContextLoc -> Store -> Store
setContextInlinedFlag (ContextLoc lg) (Store vars contexts exps) = Store vars (IM.alter f lg contexts) exps
  where
    f Nothing = error "context not in store"
    f (Just cf) = Just $ cf { cfInlined = True }

addOperandToStore :: Store -> (ExpLoc, ContextLoc, Store)
addOperandToStore (Store vars contexts exps) =
  let le = IM.size exps in
  let lg = IM.size contexts in
  (ExpLoc le, ContextLoc lg, Store vars (IM.insert lg (ContextFlags False) contexts) (IM.insert le Nothing exps))

getVarFlags :: VarLoc -> Store -> VarFlags
getVarFlags (VarLoc lx) (Store vars contexts exps) = case IM.lookup lx vars of
  Nothing -> error "var not in scope"
  Just vf -> vf

getContextFlags :: ContextLoc -> Store -> ContextFlags
getContextFlags (ContextLoc lg) (Store vars contexts exps) = case IM.lookup lg contexts of
  Nothing -> error "context not in store"
  Just cf -> cf

lookupStoreExp :: ExpLoc -> Store -> Maybe Term
lookupStoreExp (ExpLoc le) (Store vars contexts exps) = case IM.lookup le exps of
  Nothing -> error "exp not in store"
  Just e' -> e'

recordOperand :: ExpLoc -> Term -> Store -> Store
recordOperand (ExpLoc le) e' (Store vars contexts exps) = Store vars contexts (IM.insert le (Just e') exps)

newtype Cont = Cont { runCont :: Term -> Store -> Term }


-- The algorithm itself
inline :: Term -> Context -> Env -> Cont -> Store -> Term
inline (TmConst c) g r k s = case g of
  Test -> case c of
    ConstFalse -> runCont k (TmConst ConstFalse) s
    _ -> runCont k (TmConst ConstTrue) s
  Effect -> runCont k (TmConst ConstVoid) s
  _ -> runCont k (TmConst c) s
inline (TmSeq e1 e2) g r k s = inline e1 Effect r (Cont k1) s
  where
    k1 e1' s' = inline e2 g r (Cont k2) s'
      where k2 e2' s'' = runCont k (sequence e1' e2') s''
inline (TmIf e1 e2 e3) g r k s = inline e1 Test r (Cont k1) s
  where
    k1 e1' s' = case result e1' of
      TmConst ConstTrue -> inline e2 g1 r (Cont ktrue) s'
        where ktrue e2' s'' = runCont k (sequence e1' e2') s''
      TmConst ConstFalse -> inline e3 g1 r (Cont kfalse) s'
        where kfalse e3' s'' = runCont k (sequence e1' e3') s''
      _ -> inline e2 g1 r (Cont ktrue) s
        where
          ktrue e2' s' = inline e3 g1 r (Cont kfalse) s'
            where
              kfalse e3' s'' = case (e2', e3') of
                (TmConst c1, TmConst c2) | c1 == c2 -> runCont k (sequence e1' e2') s''
                _ -> runCont k (TmIf e1' e2' e3') s''
    g1 = case g of
      Applied _ _ _ -> Value
      _ -> g
inline (TmAssign ix e) g r k s =
  let ix'@(IVar x' op flags lx') = lookupEnv ix r in
  let updateStore s' = setVarAssignFlag lx' s' in
  if vfRef flags then
    inline e Effect r k s
  else
    let c = case g of { Test -> ConstTrue; _ -> ConstVoid } in
    let k1 e' s' = runCont k (sequence (TmAssign ix' e') (TmConst c)) (updateStore s') in
    inline e Value r (Cont k1) s
inline (TmCall e1 e2) g r k s = inline e1 g1 r (Cont k1) s1
  where
    op = Operand { opndExp = e2, opndEnv = r, opndLoc = le2 }
    g1 = Applied op g lg1
    (le2, lg1, s1) = addOperandToStore s
    k1 e1' s2 =
      let cf = getContextFlags lg1 s2 in
      if cfInlined cf then
        runCont k e1' s2
      else
        let k2 e2' s3 = runCont k (TmCall e1' e2') s3 in
        visit op Value (Cont k2) s2
inline (TmPrimRef p) g r k s = case g of
  Test -> runCont k (TmConst ConstTrue) s
  Effect -> runCont k (TmConst ConstVoid) s
  Value -> runCont k (TmPrimRef p) s
  Applied _ _ _ -> foldPrimRef p g r k s
inline (TmLam ix@(IVar x Nothing _ lx) e) g r k s = case g of
  Test -> runCont k (TmConst ConstTrue) s
  Effect -> runCont k (TmConst ConstVoid) s
  Value -> inline e Value r1 (Cont k1) s1
    where
      (x', lx', s1) = freshenParameter x s
      ix' = IVar x' Nothing (getVarFlags lx s) lx'
      r1 = extendEnv ix ix' r
      k1 e' s' = runCont k (TmLam ix' e') s'
  Applied _ _ _ -> foldLam ix e g r k s
inline (TmRef ix) g r k s = case g of
  Effect -> runCont k (TmConst ConstVoid) s
  _ -> case lookupEnv ix r of
    ix'@(IVar x' (Just op) (VarFlags { vfAssign = False }) lx') -> visit op Value (Cont k1) s
      where k1 e s2 = copy ix' (result e) g k s2
    ix'@(IVar _ _ _ lx') -> runCont k (TmRef ix') (setVarRefFlag lx' s)
-- What's the rule for 'letrec' expressions? I can't find it, only a prose description in sec 2.8.
inline (TmLetRec ixs e) g r k s = error "don't know how to inline letrec"
  

freshenParameter :: TmVar -> Store -> (TmVar, VarLoc, Store)
freshenParameter x (Store vars contexts exps) =
  let x' = x in -- renaming: who needs it? (Probably me.) Hmm. I don't have easy access to the in-scope set.
  let lx' = VarLoc (IM.size vars) in
  (x', lx', Store (IM.insert (IM.size vars) emptyVarFlags vars) contexts exps)


sequence :: Term -> Term -> Term
sequence (TmConst ConstVoid) e2 = e2
-- left-associate sequencing, so that 'result' can extract the final expression
-- in a single step.
sequence e1 (TmSeq e3 e4) = TmSeq (TmSeq e1 e3) e4
sequence e1 e2 = TmSeq e1 e2

result :: Term -> Term
result (TmSeq e1 e2) = e2
result e = e

visit :: Operand -> Context -> Cont -> Store -> Term
visit (Operand e r le) g k s =
  case lookupStoreExp le s of
    Nothing -> inline e g r (Cont k1) s
      where k1 e' s' = runCont k e' (recordOperand le e' s')
    Just e' -> runCont k e' s

fold :: Term -> Context -> Env -> Cont -> Store -> Term
fold (TmPrimRef p) (Applied op g1 lg) r k s = foldPrimRef p (Applied op g1 lg) r k s
fold (TmLam ix e) (Applied op g1 lg) r k s = foldLam ix e (Applied op g1 lg) r k s

foldPrimRef :: PrimOp -> Context -> Env -> Cont -> Store -> Term
foldPrimRef p (Applied op g1 lg) r k s = visit op Value (Cont k1) s
  where
    k1 e1' s1 = case result e1' of
      TmConst c -> let c' = applyPrim p c in runCont k (TmConst c') (setContextInlinedFlag lg s1)
      _ -> runCont k (TmPrimRef p) s1

foldLam :: IVar -> Term -> Context -> Env -> Cont -> Store -> Term
foldLam ix@(IVar x Nothing vf lx) e (Applied op g1 lg) r k s = inline e g1 r1 (Cont k1) s1
  where
    (x', lx', s1) = freshenParameter x s
    ix' = IVar x' Nothing (getVarFlags lx s) lx'
    r1 = extendEnv ix ix' r
    k1 e' s2 =
      let
        k2 e1' s3 = runCont k (sequence e1' e') (setContextInlinedFlag lg s3)
        -- this is basically a let-binding for the operand, since we were not able to discard it entirely.
        k3 e1' s3 = runCont k (TmCall (TmLam ix' e') e1') (setContextInlinedFlag lg s3)
      in case getVarFlags lx' s2 of
        -- no residual occurrence of ix', not assigned ==> can visit for effect, just sequence it
        VarFlags { vfRef = False, vfAssign = False } ->
          visit op Effect (Cont k2) s2
        -- ix' was assigned ==> can visit for effect, but need to insert a let-binding (basically)
        VarFlags { vfRef = False, vfAssign = True } ->
          visit op Effect (Cont k3) s2
        -- ix' appears in the residual program ==> insert a let-binding for the operand.
        VarFlags { vfRef = True, vfAssign = _ } ->
          visit op Value (Cont k3) s2

copy :: IVar -> Term -> Context -> Cont -> Store -> Term
copy ix'@(IVar x' op vf lx') e g k s = case (e, g) of
  -- because constants are closed, we can materialize an empty env to inline this constant
  (TmConst c, _) -> inline (TmConst c) g emptyEnv k s
  (TmRef ix1@(IVar x1 op1 (VarFlags { vfAssign = False }) lx1), _) -> runCont k (TmRef ix1) s
  (TmPrimRef p, Applied op1 g1 lg) -> foldPrimRef p (Applied op1 g1 lg) emptyEnv k s -- primrefs are closed, no need for env
  (TmLam ix1 e1, Applied op1 g1 lg) -> foldLam ix1 e1 (Applied op1 g1 lg) emptyEnv k s -- do we know that this lambda is closed? More pertinently, how do we know that we don't need to do any renaming here?
  (TmPrimRef p, Test) -> runCont k (TmConst ConstTrue) s
  (TmAssign x1 e1, Test) -> runCont k (TmConst ConstTrue) s
  (TmLam x1 e1, Test) -> runCont k (TmConst ConstTrue) s
  (_, _) -> runCont k (TmRef ix') (setVarRefFlag lx' s)


-- Hrrm. The IR as it stands is almost to sparse to give meaningful examples
-- ALSO, there's the whole thing about effort counter and size counter that I
-- need to start caring about.
-- raw :: RawTerm
-- raw = _

main :: IO ()
main = putStrLn "Hello, World!"
