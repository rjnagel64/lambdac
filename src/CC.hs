{-# LANGUAGE DerivingStrategies, GeneralizedNewtypeDeriving #-}

module CC
  ( TermC(..)
  , ClosureDef(..)
  , ContClosureDef(..)
  , Name(..)
  , ValueC(..)

  , cconv
  , pprintTerm
  ) where

import qualified Data.Set as Set
import Data.Set (Set)

import Data.List (intercalate)

import qualified CPS as K
import CPS (TermK(..), FunDef(..), ContDef(..), ValueK(..))

-- Closure conversion:
-- https://gist.github.com/jozefg/652f1d7407b7f0266ae9
--
-- Example:
-- let a = 4; b = 3; in let f = \x -> \y -> a*x + b*y in f 2 5
-- let a = 4; b = 3; in
--   let
--     f = <{a := a, b := b}, \x -> <{a := a, b := b, x = x}, \y -> a*x + b*y>>;
--   in
--     f 2 5

-- Note: [Closure Conversion and Lifting]
-- After closure conversion, every lambda is annotated with its free variables.
-- If there are no free variables, the lambda can be trivially lifted to the top level.
-- If there are free variables, [Selective Lambda Lifting.pdf] can optionally
-- lift if it would be beneficial.
-- However, not all closures can/should be lifted. For example, consider a
-- lambda in a loop, that captures a different value of 'n' each time.
--
-- For compilation, there is still some "hoisting" that needs to be done,
-- because the code pointer for each lambda needs to be defined at the top
-- level, and also because the struct for the captured variables needs to be
-- hoisted too.

-- cconvTy :: TypeK -> TypeC
-- cconvTy (a -> b) = ∃c. (c -> cconvTy a -> cconvTy b) × c
-- (actually, CPS types rather than a -> b, but approximately.)
-- (Also, this version tends to have lots of fst/snd from nested pairs. Could
-- do n-ary tuples instead.)

-- The sort of a name can be determined from where it is bound.
newtype Name = Name String
  deriving (Eq, Ord)

instance Show Name where
  show (Name x) = x

tmVar :: K.TmVar -> Name
tmVar (K.TmVar x) = Name x

coVar :: K.CoVar -> Name
coVar (K.CoVar k) = Name k

fnName :: K.FnName -> Name
fnName (K.FnName f) = Name f

-- Closure conversion is bottom-up (to get flat closures) traversal that
-- replaces free variables with references to an environment parameter.
data TermC
  = LetValC Name ValueC TermC -- let x = v in e, allocation
  | LetFstC Name Name TermC -- let x = fst y in e, projection
  | LetSndC Name Name TermC
  | LetAddC Name Name Name TermC
  | LetIsZeroC Name Name TermC
  | LetFunC [ClosureDef] TermC
  | LetContC [ContClosureDef] TermC
  -- Invoke a closure by providing a value for the only remaining argument.
  | JumpC Name Name -- k x
  | CallC Name Name Name -- f x k
  | HaltC Name
  | CaseC Name Name Name -- case x of k1 | k2

-- | @f {x+} y k = e@
-- Closures capture two sets of names: those from outer scopes, and those from
-- the same recursive bind group.
data ClosureDef
  = ClosureDef {
    closureName :: Name
  , closureFreeNames :: [Name]
  , closureRecNames :: [Name]
  , closureParam :: Name
  , closureCont :: Name
  , closureBody :: TermC
  }

-- | @k {x+} y = e@
-- Closures capture two sets of names: those from outer scopes, and those from
-- the same recursive bind group.
data ContClosureDef
  = ContClosureDef {
    contClosureName :: Name
  , contClosureFreeNames :: [Name]
  , contClosureRecNames :: [Name]
  , contClosureParam :: Name
  , contClosureBody :: TermC
  }

data ValueC
  = PairC Name Name
  | InlC Name
  | InrC Name
  | NilC
  | IntC Int

-- @(free, inBindGroup)@.
newtype EnvVars = EnvVars (Set Name, Set Name)
  deriving newtype (Semigroup, Monoid)

-- | @bound -> binding -> (free, inBinding)@
-- @binding@ is the nearest enclosing group of recursive bindings.
newtype Env = Env { runEnv :: Set Name -> EnvVars }

instance Semigroup Env where
  Env f <> Env g = Env $ \binding -> f binding <> g binding

instance Monoid Env where
  mempty = Env $ \_ -> mempty

bindRec :: [Name] -> Env -> Env
bindRec xs vs = Env $ \binding -> case runEnv vs binding of
  -- Any variable in 'free' that refers to xs is a bound occurrence.
  -- Any variable in 'rec' that refers to xs is not a reference to the current
  -- bind group.
  EnvVars (free, rec) -> EnvVars (free Set.\\ xs', rec Set.\\ xs')
  where xs' = Set.fromList xs

bind :: [Name] -> Env -> Env
bind xs vs = Env $ \binding -> case runEnv vs binding of
  EnvVars (free, rec) -> EnvVars (free Set.\\ xs', rec Set.\\ xs')
  where xs' = Set.fromList xs

unit :: Name -> Env
unit x = Env $ \binding ->
  if Set.member x binding then
    EnvVars (Set.empty, Set.singleton x)
  else
    EnvVars (Set.singleton x, Set.empty)

class Close a where
  -- TODO: Better name. This is still a free variable traversal, really.
  -- It doesn't do that actual work of "closing", as that's in 'cconv'.
  close :: a -> Env

instance Close TermK where
  close (HaltK x) = unit (tmVar x)
  close (JumpK k x) = unit (coVar k) <> unit (tmVar x)
  close (LetValK x v e) = close v <> bind [tmVar x] (close e)
  close (CallK f x k) = unit (fnName f) <> unit (tmVar x) <> unit (coVar k)
  close (CaseK x k1 k2) = unit (tmVar x) <> unit (coVar k1) <> unit (coVar k2)
  close (LetFstK x y e) = unit (tmVar y) <> bind [tmVar x] (close e)
  close (LetSndK x y e) = unit (tmVar y) <> bind [tmVar x] (close e)
  close (LetIsZeroK x y e) = unit (tmVar y) <> bind [tmVar x] (close e)
  close (LetAddK z x y e) = unit (tmVar x) <> unit (tmVar y) <> bind [tmVar z] (close e)
  close (LetFunK fs e) = foldMap g fs <> bind fs' (close e)
    where
      -- In each definition, all the all definitions and also the parameters are in scope.
      g :: FunDef -> Env
      g (FunDef _f x k e') = bindRec fs' $ bind [tmVar x, coVar k] $ close e'
      fs' :: [Name]
      fs' = map (\ (FunDef f _ _ _) -> fnName f) fs
  close (LetContK ks e) = foldMap g ks <> bind ks' (close e)
    where
      -- In each definition, all the all definitions and also the parameters are in scope.
      g :: ContDef -> Env
      g (ContDef _k x e') = bindRec ks' $ bind [tmVar x] $ close e'
      ks' :: [Name]
      ks' = map (\ (ContDef k _ _) -> coVar k) ks

instance Close ValueK where
  close NilK = mempty
  close (IntK _) = mempty
  close (InlK x) = unit (tmVar x)
  close (InrK y) = unit (tmVar y)
  close (PairK x y) = unit (tmVar x) <> unit (tmVar y)

instance Close FunDef where
  close (FunDef f x k e) = bind [fnName f, tmVar x, coVar k] $ close e

instance Close ContDef where
  close (ContDef k x e) = bind [coVar k, tmVar x] $ close e

-- TODO: Recursive occurrences count as free variables, because they need to be
-- present in the closure environment.
-- TODO: Occurrences from the same recursive bind group should be stored separately.
cconv :: TermK -> TermC
cconv (LetFunK fs e) = LetFunC (map ann fs) (cconv e)
  where
    -- TODO: Recursive occurrences count a free occurrences.
    ann fun@(FunDef f x k e') =
      let EnvVars (vs, vs') = runEnv (close fun) fs' in
      ClosureDef (fnName f) (Set.toList vs) (Set.toList vs') (tmVar x) (coVar k) (cconv e')
    fs' = Set.fromList $ map (\ (FunDef f _ _ _) -> fnName f) fs
cconv (LetContK ks e) = LetContC (map ann ks) (cconv e)
  where
    ann kont@(ContDef k x e') =
      let EnvVars (vs, vs') = runEnv (close kont) ks' in
      ContClosureDef (coVar k) (Set.toList vs) (Set.toList vs') (tmVar x) (cconv e')
    ks' = Set.fromList $ map (\ (ContDef k _ _) -> coVar k) ks
cconv (HaltK x) = HaltC (tmVar x)
cconv (JumpK k x) = JumpC (coVar k) (tmVar x)
cconv (CallK f x k) = CallC (fnName f) (tmVar x) (coVar k)
cconv (CaseK x k1 k2) = CaseC (tmVar x) (coVar k1) (coVar k2)
cconv (LetFstK x y e) = LetFstC (tmVar x) (tmVar y) (cconv e)
cconv (LetSndK x y e) = LetSndC (tmVar x) (tmVar y) (cconv e)
cconv (LetIsZeroK x y e) = LetIsZeroC (tmVar x) (tmVar y) (cconv e)
cconv (LetValK x v e) = LetValC (tmVar x) (cconvValue v) (cconv e)
cconv (LetAddK z x y e) = LetAddC (tmVar z) (tmVar x) (tmVar y) (cconv e)

cconvValue :: ValueK -> ValueC
cconvValue NilK = NilC
cconvValue (PairK x y) = PairC (tmVar x) (tmVar y)
cconvValue (IntK i) = IntC i
cconvValue (InlK x) = InlC (tmVar x)
cconvValue (InrK y) = InrC (tmVar y)

-- What does well-typed closure conversion look like?
-- How are the values in a closure bound?

-- Closure conversion is not lambda lifting.
-- CC involves capturing the environment when a function is created (but the
-- call site remains mostly the same), LL requires altering the call sites.
-- (LL is O(n^3) or O(n^2), CC is less?)
-- https://pages.github.ccs.neu.edu/jhemann/21SP-CS4400/FAQ/closure-conv/


indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintTerm :: Int -> TermC -> String
pprintTerm n (HaltC x) = indent n $ "HALT " ++ show x ++ ";\n"
pprintTerm n (JumpC k x) = indent n $ show k ++ " " ++ show x ++ ";\n"
pprintTerm n (CallC f x k) = indent n $ show f ++ " " ++ show x ++ " " ++ show k ++ ";\n"
pprintTerm n (LetFunC fs e) =
  indent n "letfun\n" ++ concatMap (pprintClosureDef (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetContC fs e) =
  indent n "letcont\n" ++ concatMap (pprintContClosureDef (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetValC x v e) =
  indent n ("let " ++ show x ++ " = " ++ pprintValue v ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetFstC x y e) =
  indent n ("let " ++ show x ++ " = fst " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetSndC x y e) =
  indent n ("let " ++ show x ++ " = snd " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetIsZeroC x y e) =
  indent n ("let " ++ show x ++ " = iszero " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (CaseC x k1 k2) =
  indent n $ "case " ++ show x ++ " of " ++ show k1 ++ " | " ++ show k2 ++ ";\n"
pprintTerm n (LetAddC z x y e) =
  indent n ("let " ++ show z ++ " = " ++ show x ++ " + " ++ show y ++ ";\n") ++ pprintTerm n e

pprintValue :: ValueC -> String
pprintValue NilC = "()"
pprintValue (PairC x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue (IntC i) = show i
pprintValue (InlC x) = "inl " ++ show x
pprintValue (InrC y) = "inr " ++ show y

pprintClosureDef :: Int -> ClosureDef -> String
pprintClosureDef n (ClosureDef f free rec x k e) =
  indent n env ++ indent n (show f ++ " " ++ show x ++ " " ++ show k ++ " =\n") ++ pprintTerm (n+2) e
  where
    env = "{" ++ intercalate ", " vars ++ "}\n"
    vars = map show (free ++ rec)

pprintContClosureDef :: Int -> ContClosureDef -> String
pprintContClosureDef n (ContClosureDef k free rec x e) =
  indent n env ++ indent n (show k ++ " " ++ show x ++ " =\n") ++ pprintTerm (n+2) e
  where
    env = "{" ++ intercalate ", " vars ++ "}\n"
    vars = map show (free ++ rec)
