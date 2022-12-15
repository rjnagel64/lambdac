{-# LANGUAGE
    DerivingStrategies
  , GeneralizedNewtypeDeriving
  , StandaloneDeriving
  , FlexibleInstances
  , MultiParamTypeClasses
  #-}

module CC.IR
  ( TermC(..)
  , Argument(..)
  , CaseKind(..)
  , FunClosureDef(..)
  , funClosureSort
  , ClosureParam(..)
  , makeClosureParams
  , ContClosureDef(..)
  , contClosureSort
  , EnvDef(..)
  , Name(..)
  , prime
  , ValueC(..)
  , ArithC(..)
  , CmpC(..)
  , Sort(..)
  , TeleEntry(..)
  , TyVar(..)

  , pprintProgram
  ) where

import Data.List (intercalate)

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

-- Closure conversion is not lambda lifting.
-- CC involves capturing the environment when a function is created (but the
-- call site remains mostly the same), LL requires altering the call sites.
-- (LL is O(n^3) or O(n^2), CC is less?)
-- https://pages.github.ccs.neu.edu/jhemann/21SP-CS4400/FAQ/closure-conv/

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

-- Idea: I could factor out the fv computation by first doing a annotation pass
-- over the data, and then having 'cconv :: TermK EnvFields -> ConvM TermC'.
-- This does get a bit messy with both TmVar/CoVar and Name being present,
-- though, so I'll stick with the current approach.

-- What does well-typed closure conversion look like?
-- How are the values in a closure bound?


-- The sort of a name can be determined from where it is bound.
data Name = Name String Int
  deriving (Eq, Ord)

instance Show Name where
  show (Name x i) = x ++ show i

prime :: Name -> Name
prime (Name x i) = Name x (i+1)

data TyVar = TyVar String
  deriving (Eq, Ord)

instance Show TyVar where
  show (TyVar aa) = aa

-- | 'Sort' is really just the CC equivalent of a type.
-- (The different name exists mostly for historical reasons)
data Sort
  = Closure [TeleEntry]
  | Integer
  | Alloc TyVar
  | Sum
  | String
  | Pair Sort Sort
  | Unit
  | Boolean
  | List Sort

data TeleEntry
  = ValueTele Sort
  | TypeTele TyVar

-- Closure conversion is bottom-up (to get flat closures) traversal that
-- replaces free variables with references to an environment parameter.
data TermC
  = LetValC (Name, Sort) ValueC TermC -- let x = v in e, allocation
  | LetFstC (Name, Sort) Name TermC -- let x = fst y in e, projection
  | LetSndC (Name, Sort) Name TermC
  | LetArithC (Name, Sort) ArithC TermC
  | LetNegateC (Name, Sort) Name TermC -- let x = -y in e, unary negation
  | LetCompareC (Name, Sort) CmpC TermC
  | LetConcatC (Name, Sort) Name Name TermC -- let x = y ++ z in e, concatenation
  | LetFunC [FunClosureDef] TermC
  | LetContC [ContClosureDef] TermC
  -- Invoke a closure by providing values for the remaining arguments.
  | JumpC Name [Name] -- k x...
  | CallC Name [Argument] [Name] -- f (x | @t)+ k+
  | HaltC Name
  | CaseC Name CaseKind [Name] -- case x of k1 | k2 | ...

data Argument = ValueArg Name | TypeArg Sort

data CaseKind
  = CaseBool
  | CaseSum Sort Sort
  | CaseList Sort

data ArithC
  = AddC Name Name
  | SubC Name Name
  | MulC Name Name

data CmpC
  = EqC Name Name
  | NeC Name Name
  | LtC Name Name
  | LeC Name Name
  | GtC Name Name
  | GeC Name Name

-- | A function definition, @f {aa+; x+} y+ k+ = e@.
-- Both type and term parameters are permitted in the parameter list.
data FunClosureDef
  = FunClosureDef {
    funClosureName :: Name
  , funEnvDef :: EnvDef
  , funClosureParams :: [ClosureParam]
  , funClosureBody :: TermC
  }

funClosureSort :: FunClosureDef -> Sort
funClosureSort (FunClosureDef _ _ params _) = paramsSort params

data ClosureParam = TypeParam TyVar | ValueParam Name Sort

makeClosureParams :: [TyVar] -> [(Name, Sort)] -> [ClosureParam]
makeClosureParams aas xs = map TypeParam aas ++ map (uncurry ValueParam) xs

paramsSort :: [ClosureParam] -> Sort
paramsSort params = Closure (map f params)
  where
    f (TypeParam aa) = TypeTele aa
    f (ValueParam _ s) = ValueTele s

-- | A continuation definition, @k {aa+; x+} y+ = e@.
data ContClosureDef
  = ContClosureDef {
    contClosureName :: Name
  , contEnvDef :: EnvDef
  -- Eventually, continuation closures will need to take type arguments as well.
  -- Specifically, this is required when unpacking existential types.
  -- However, I'm not quite sure that making contClosureParams a full-on
  -- parameter telescope is the correct way to go.
  -- In particular, I *think* we should always be able to segregate it into a
  -- type params, followed by value params.
  , contClosureParams :: [(Name, Sort)]
  , contClosureBody :: TermC
  }

contClosureSort :: ContClosureDef -> Sort
contClosureSort (ContClosureDef _ _ params _) = paramsSort (makeClosureParams [] params)

-- | Closures environments capture two sets of names: those from outer scopes,
-- and those from the same recursive bind group.
data EnvDef
  = EnvDef {
    envFreeTypes :: [TyVar]
  , envFreeNames :: [(Name, Sort)]
  }

data ValueC
  = PairC Name Name
  | NilC
  | InlC Name
  | InrC Name
  | IntC Int
  | BoolC Bool
  | EmptyC
  | ConsC Name Name
  | StringC String


indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintProgram :: TermC -> String
pprintProgram e = pprintTerm 0 e

pprintTerm :: Int -> TermC -> String
pprintTerm n (HaltC x) = indent n $ "HALT " ++ show x ++ ";\n"
pprintTerm n (JumpC k xs) = indent n $ show k ++ " " ++ intercalate " " (map show xs) ++ ";\n"
pprintTerm n (CallC f xs ks) =
  indent n $ show f ++ " " ++ intercalate " " (map pprintArg xs ++ map show ks) ++ ";\n"
  where
    pprintArg (ValueArg x) = show x
    pprintArg (TypeArg t) = pprintSort t
pprintTerm n (LetFunC fs e) =
  indent n "letfun\n" ++ concatMap (pprintFunClosureDef (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetContC fs e) =
  indent n "letcont\n" ++ concatMap (pprintContClosureDef (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetValC x v e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintValue v ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetFstC x y e) =
  indent n ("let " ++ pprintPlace x ++ " = fst " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetSndC x y e) =
  indent n ("let " ++ pprintPlace x ++ " = snd " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (CaseC x _ ks) =
  let branches = intercalate " | " (map show ks) in
  indent n $ "case " ++ show x ++ " of " ++ branches ++ ";\n"
pprintTerm n (LetArithC x op e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintArith op ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetNegateC x y e) =
  indent n ("let " ++ pprintPlace x ++ " = -" ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetCompareC x cmp e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintCompare cmp ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetConcatC x y z e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ show y ++ " ++ " ++ show z ++ ";\n") ++ pprintTerm n e

pprintSort :: Sort -> String
pprintSort (Closure ss) = "(" ++ intercalate ", " (map pprintTele ss) ++ ") -> !"
pprintSort Integer = "int"
pprintSort (Alloc aa) = "alloc(" ++ show aa ++ ")"
pprintSort Sum = "sum"
pprintSort String = "string"
pprintSort Boolean = "bool"
pprintSort (List s) = "list " ++ pprintSort s
pprintSort (Pair s t) = "pair " ++ pprintSort s ++ " " ++ pprintSort t
pprintSort Unit = "unit"

pprintTele :: TeleEntry -> String
pprintTele (ValueTele s) = pprintSort s
pprintTele (TypeTele aa) = '@' : show aa

pprintPlace :: (Name, Sort) -> String
pprintPlace (x, s) = show x ++ " : " ++ pprintSort s

pprintValue :: ValueC -> String
pprintValue NilC = "()"
pprintValue (PairC x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue (IntC i) = show i
pprintValue (BoolC b) = if b then "true" else "false"
pprintValue (InlC x) = "inl " ++ show x
pprintValue (InrC y) = "inr " ++ show y
pprintValue EmptyC = "nil"
pprintValue (ConsC x xs) = "cons " ++ show x ++ " " ++ show xs
pprintValue (StringC s) = show s

pprintArith :: ArithC -> String
pprintArith (AddC x y) = show x ++ " + " ++ show y
pprintArith (SubC x y) = show x ++ " - " ++ show y
pprintArith (MulC x y) = show x ++ " * " ++ show y

pprintCompare :: CmpC -> String
pprintCompare (EqC x y) = show x ++ " == " ++ show y
pprintCompare (NeC x y) = show x ++ " != " ++ show y
pprintCompare (LtC x y) = show x ++ " < " ++ show y
pprintCompare (LeC x y) = show x ++ " <= " ++ show y
pprintCompare (GtC x y) = show x ++ " > " ++ show y
pprintCompare (GeC x y) = show x ++ " >= " ++ show y

pprintFunClosureDef :: Int -> FunClosureDef -> String
pprintFunClosureDef n (FunClosureDef f env params e) =
  pprintEnvDef n env ++
  indent n (show f ++ " (" ++ pprintClosureParams params ++ ") =\n") ++ pprintTerm (n+2) e

pprintContClosureDef :: Int -> ContClosureDef -> String
pprintContClosureDef n (ContClosureDef k env xs e) =
  pprintEnvDef n env ++ indent n (show k ++ " " ++ params ++ " =\n") ++ pprintTerm (n+2) e
  where
    params = "(" ++ intercalate ", " args ++ ")"
    args = map pprintPlace xs

pprintClosureParams :: [ClosureParam] -> String
pprintClosureParams params = intercalate ", " (map f params)
  where
    f (TypeParam aa) = "@" ++ show aa
    f (ValueParam x s) = pprintPlace (x, s)

pprintEnvDef :: Int -> EnvDef -> String
pprintEnvDef n (EnvDef tys free) = indent n $ "{" ++ intercalate ", " vars ++ "}\n"
  where
    vars = map (\v -> "@" ++ show v) tys ++ map pprintPlace free
