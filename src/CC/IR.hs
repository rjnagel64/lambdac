
module CC.IR
  ( Program(..)
  , DataDecl(..)
  , CtorDecl(..)

  , Name(..)
  , prime
  , TyVar(..)
  , TyCon(..)
  , Ctor(..)
  , FieldLabel(..)

  , TermC(..)
  , ValueC(..)
  , ArithC(..)
  , CmpC(..)
  , StringOpC(..)
  , PrimIO(..)
  , Argument(..)
  , TyConApp(..)
  , FunClosureDef(..)
  , funClosureSort
  , ClosureParam(..)
  , makeClosureParams
  , ContClosureDef(..)
  , contClosureSort
  , EnvDef(..)
  , Sort(..)
  , TeleEntry(..)

  , Kind(..)

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

data TyCon = TyCon String

instance Show TyCon where
  show (TyCon tc) = tc

data Ctor = Ctor String

instance Show Ctor where
  show (Ctor c) = c

newtype FieldLabel = FieldLabel String

instance Show FieldLabel where
  show (FieldLabel f) = f

-- | 'Sort' is really just the CC equivalent of a type.
-- (The different name exists mostly for historical reasons)
data Sort
  = Closure [TeleEntry]
  | Integer
  | Alloc TyVar
  | String
  | Character
  | Pair Sort Sort
  | Record [(FieldLabel, Sort)]
  | Unit
  | Boolean
  | TyConOcc TyCon
  | TyApp Sort Sort
  | Token

data TeleEntry
  = ValueTele Sort
  | TypeTele TyVar Kind

data Kind
  = Star
  | KArr Kind Kind

data Program = Program [DataDecl] TermC

data DataDecl
  = DataDecl TyCon [(TyVar, Kind)] [CtorDecl]

data CtorDecl
  = CtorDecl Ctor [Sort]

-- Closure conversion is bottom-up (to get flat closures) traversal that
-- replaces free variables with references to an environment parameter.
data TermC
  = LetValC (Name, Sort) ValueC TermC -- let x = v in e, allocation
  | LetFstC (Name, Sort) Name TermC -- let x = fst y in e, projection
  | LetSndC (Name, Sort) Name TermC
  | LetFieldC (Name, Sort) Name FieldLabel TermC -- let x = y#field in e, projection
  | LetArithC (Name, Sort) ArithC TermC
  | LetCompareC (Name, Sort) CmpC TermC
  | LetStringOpC (Name, Sort) StringOpC TermC
  | LetBindC (Name, Sort) (Name, Sort) PrimIO TermC
  | LetFunC [FunClosureDef] TermC
  | LetContC [(Name, ContClosureDef)] TermC
  -- Invoke a closure by providing values for the remaining arguments.
  | JumpC Name [Name] -- k x...
  | CallC Name [Argument] [Name] -- f (x | @t)+ k+
  | HaltC Name
  | IfC Name Name Name -- if x then k1 else k2
  | CaseC Name TyConApp [(Ctor, Name)] -- case x of c1 -> k1 | c2 -> k2 | ...

data Argument = ValueArg Name | TypeArg Sort

data TyConApp = TyConApp TyCon [Sort]

data ArithC
  = AddC Name Name
  | SubC Name Name
  | MulC Name Name
  | NegC Name

data CmpC
  = EqC Name Name
  | NeC Name Name
  | LtC Name Name
  | LeC Name Name
  | GtC Name Name
  | GeC Name Name
  | EqCharC Name Name

data StringOpC
  = ConcatC Name Name -- y ^ z, concatenation
  | IndexC Name Name -- char_at_index x i, indexing

data PrimIO
  = GetLineC Name
  | PutLineC Name Name

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

data ClosureParam = TypeParam TyVar Kind | ValueParam Name Sort

makeClosureParams :: [(TyVar, Kind)] -> [(Name, Sort)] -> [ClosureParam]
makeClosureParams aas xs = map (uncurry TypeParam) aas ++ map (uncurry ValueParam) xs

paramsSort :: [ClosureParam] -> Sort
paramsSort params = Closure (map f params)
  where
    f (TypeParam aa k) = TypeTele aa k
    f (ValueParam _ s) = ValueTele s

-- | A continuation definition, @k {aa+; x+} y+ = e@.
data ContClosureDef
  = ContClosureDef {
    contEnvDef :: EnvDef
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
contClosureSort (ContClosureDef _ params _) = paramsSort (makeClosureParams [] params)

-- | Closures environments capture two sets of names: those from outer scopes,
-- and those from the same recursive bind group.
data EnvDef
  = EnvDef {
    envFreeTypes :: [(TyVar, Kind)]
  , envFreeNames :: [(Name, Sort)]
  }

data ValueC
  = PairC Name Name
  | RecordC [(FieldLabel, Name)]
  | NilC
  | WorldTokenC
  | IntC Int
  | BoolC Bool
  | StringC String
  | CharC Char
  | CtorAppC Ctor [Name]


indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintProgram :: Program -> String
pprintProgram (Program ds e) = concatMap (pprintDataDecl 0) ds ++ pprintTerm 0 e

pprintDataDecl :: Int -> DataDecl -> String
pprintDataDecl n (DataDecl tc params ctors) =
  indent n $ "data " ++ show tc ++ intercalate " " (map f params) ++ " where\n" ++
  unlines (map (pprintCtorDecl (n+2)) ctors)
  where f (aa, k) = "(" ++ show aa ++ " : " ++ pprintKind k ++ ")"

pprintCtorDecl :: Int -> CtorDecl -> String
pprintCtorDecl n (CtorDecl c args) =
  indent n $ show c ++ "(" ++ intercalate ", " (map pprintSort args) ++ ")"

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
pprintTerm n (LetContC ks e) =
  indent n "letcont\n" ++ concatMap (pprintContClosureDef (n+2)) ks ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetValC x v e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintValue v ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetFstC x y e) =
  indent n ("let " ++ pprintPlace x ++ " = fst " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetSndC x y e) =
  indent n ("let " ++ pprintPlace x ++ " = snd " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetFieldC x y f e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ show y ++ "#" ++ show f ++ ";\n") ++ pprintTerm n e
pprintTerm n (IfC x k1 k2) =
  indent n $ "if " ++ show x ++ " then " ++ show k1 ++ " else " ++ show k2
pprintTerm n (CaseC x _ ks) =
  let branches = intercalate " | " (map show ks) in
  indent n $ "case " ++ show x ++ " of " ++ branches ++ ";\n"
pprintTerm n (LetArithC x op e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintArith op ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetCompareC x cmp e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintCompare cmp ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetStringOpC x op e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintStringOp op ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetBindC x y prim e) =
  indent n ("let " ++ pprintPlace x ++ ", " ++ pprintPlace y ++ " = " ++ pprintPrimIO prim ++ ";\n") ++ pprintTerm n e

pprintSort :: Sort -> String
pprintSort (Closure ss) = "(" ++ intercalate ", " (map pprintTele ss) ++ ") -> !"
pprintSort Integer = "int"
pprintSort (Alloc aa) = "alloc(" ++ show aa ++ ")"
pprintSort String = "string"
pprintSort Character = "char"
pprintSort Boolean = "bool"
pprintSort (Pair s t) = "pair " ++ pprintSort s ++ " " ++ pprintSort t
pprintSort (Record []) = "{}"
pprintSort (Record fs) = "{ " ++ intercalate ", " (map pprintField fs) ++ " }"
  where pprintField (f, t) = show f ++ " : " ++ pprintSort t
pprintSort Unit = "unit"
pprintSort Token = "token#"
pprintSort (TyConOcc tc) = show tc
pprintSort (TyApp s t) = pprintSort s ++ " " ++ pprintSort t

pprintTele :: TeleEntry -> String
pprintTele (ValueTele s) = pprintSort s
pprintTele (TypeTele aa k) = '@' : show aa ++ " : " ++ pprintKind k

pprintKind :: Kind -> String
pprintKind Star = "*"
pprintKind (KArr Star k2) = "* -> " ++ pprintKind k2
pprintKind (KArr k1 k2) = "(" ++ pprintKind k1 ++ ") -> " ++ pprintKind k2

pprintPlace :: (Name, Sort) -> String
pprintPlace (x, s) = show x ++ " : " ++ pprintSort s

pprintValue :: ValueC -> String
pprintValue NilC = "()"
pprintValue WorldTokenC = "WORLD#"
pprintValue (PairC x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue (RecordC []) = "{}"
pprintValue (RecordC fs) = "{ " ++ intercalate ", " (map pprintField fs) ++ " }"
  where pprintField (f, x) = show f ++ " = " ++ show x
pprintValue (IntC i) = show i
pprintValue (BoolC b) = if b then "true" else "false"
pprintValue (StringC s) = show s
pprintValue (CharC c) = show c
pprintValue (CtorAppC c xs) = show c ++ "(" ++ intercalate ", " (map show xs) ++ ")"

pprintArith :: ArithC -> String
pprintArith (AddC x y) = show x ++ " + " ++ show y
pprintArith (SubC x y) = show x ++ " - " ++ show y
pprintArith (MulC x y) = show x ++ " * " ++ show y
pprintArith (NegC x) = "- " ++ show x

pprintCompare :: CmpC -> String
pprintCompare (EqC x y) = show x ++ " == " ++ show y
pprintCompare (NeC x y) = show x ++ " != " ++ show y
pprintCompare (LtC x y) = show x ++ " < " ++ show y
pprintCompare (LeC x y) = show x ++ " <= " ++ show y
pprintCompare (GtC x y) = show x ++ " > " ++ show y
pprintCompare (GeC x y) = show x ++ " >= " ++ show y
pprintCompare (EqCharC x y) = show x ++ " == " ++ show y

pprintStringOp :: StringOpC -> String
pprintStringOp (ConcatC x y) = show x ++ " ^ " ++ show y
pprintStringOp (IndexC x y) = show x ++ ".char_at_index " ++ show y

pprintPrimIO :: PrimIO -> String
pprintPrimIO (GetLineC x) = "getLine " ++ show x
pprintPrimIO (PutLineC x y) = "putLine " ++ show x ++ " " ++ show y

pprintFunClosureDef :: Int -> FunClosureDef -> String
pprintFunClosureDef n (FunClosureDef f env params e) =
  pprintEnvDef n env ++
  indent n (show f ++ " (" ++ pprintClosureParams params ++ ") =\n") ++ pprintTerm (n+2) e

pprintContClosureDef :: Int -> (Name, ContClosureDef) -> String
pprintContClosureDef n (k, ContClosureDef env xs e) =
  pprintEnvDef n env ++ indent n (show k ++ " " ++ params ++ " =\n") ++ pprintTerm (n+2) e
  where
    params = "(" ++ intercalate ", " args ++ ")"
    args = map pprintPlace xs

pprintClosureParams :: [ClosureParam] -> String
pprintClosureParams params = intercalate ", " (map f params)
  where
    f (TypeParam aa k) = '@' : show aa ++ " : " ++ pprintKind k
    f (ValueParam x s) = pprintPlace (x, s)

pprintEnvDef :: Int -> EnvDef -> String
pprintEnvDef n (EnvDef tys free) = indent n $ "{" ++ intercalate ", " vars ++ "}\n"
  where
    vars = map (\ (aa, k) -> '@' : show aa ++ " : " ++ pprintKind k) tys ++ map pprintPlace free
