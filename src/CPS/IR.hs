
module CPS.IR
    ( Program(..)
    , DataDecl(..)
    , CtorDecl(..)

    , TermK(..)
    , ArithK(..)
    , CmpK(..)
    , StringOpK(..)
    , ValueK(..)
    , CoValueK(..)
    , PrimIO(..)

    , TmVar(..)
    , CoVar(..)
    , TyVar(..)
    , TyCon(..)
    , Ctor(..)
    , FieldLabel(..)

    , FunDef(..)
    , funDefName
    , funDefType
    , ContDef(..)
    , contDefType

    , TypeK(..)
    , eqTypeK
    , CoTypeK(..)
    , eqCoTypeK
    , TyConApp(..)
    , asTyConApp
    , fromTyConApp

    , KindK(..)

    , Subst
    , listSubst
    , substTypeK
    , substCoTypeK
    , substTyConApp

    , pprintProgram
    , pprintType
    , pprintCoType
    , pprintKind
    , pprintValue
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.List (intercalate)
import Data.Traversable (mapAccumL)

-- All sorts of variables exist in the same namespace.
-- Continuations are second-class, so they get a different type. (I collapse
-- the distinction between them later on, but maybe there's a more efficient
-- way to do jumps...)
data TmVar = TmVar String Int
  deriving (Eq, Ord)
data CoVar = CoVar String Int
  deriving (Eq, Ord)
data TyVar = TyVar String Int
  deriving (Eq, Ord)

instance Show TmVar where
  show (TmVar x i) = x ++ show i
instance Show CoVar where
  show (CoVar k i) = k ++ show i
instance Show TyVar where
  show (TyVar a i) = a ++ show i

data TyCon = TyCon String
  deriving (Eq, Ord)
data Ctor = Ctor String
  deriving (Eq, Ord)

instance Show TyCon where
  show (TyCon tc) = tc
instance Show Ctor where
  show (Ctor c) = c

newtype FieldLabel = FieldLabel String
  deriving Eq

instance Show FieldLabel where
  show (FieldLabel f) = f


data Program = Program [DataDecl] TermK

data DataDecl = DataDecl TyCon KindK [CtorDecl]

data CtorDecl = CtorDecl Ctor [(TyVar, KindK)] [TypeK]

-- | Terms in continuation-passing style.
--
-- CPS terms are basically (named, parametrized) basic blocks: a list of
-- assignments terminated by a control flow transfer.
--
-- (Actually, I think this IR is technically or nearly in ANF)
--
-- Note: This IR is not in "true" CPS, where all control flow uses
-- continuations. In particular, values and primitive operations use an
-- implicit "straight-line code" continuation that passes control to the next
-- statement. For example, @let x = y + z in e@ should actually be
-- @primcall (+) (y, z) (cont x => e)@.
--
-- The reason for this divergence is to reduce the number of closures and tail
-- calls required by the C backend, as I do not have particularly efficient
-- generated code.
data TermK
  -- Assignments
  -- let val x:t = v in e
  = LetValK TmVar TypeK ValueK TermK
  -- let x:t = fst y in e
  | LetFstK TmVar TypeK TmVar TermK
  -- let x:t = snd y in e
  | LetSndK TmVar TypeK TmVar TermK
  -- let x:t = y#field in e
  | LetFieldK TmVar TypeK TmVar FieldLabel TermK
  -- let z = x `op` y in e
  | LetArithK TmVar ArithK TermK
  -- let z = x `cmp` y in e 
  | LetCompareK TmVar CmpK TermK
  | LetStringOpK TmVar TypeK StringOpK TermK
  -- let s, x <- io_op in e
  | LetBindK TmVar TmVar PrimIO TermK

  -- let ks in e
  | LetContK [(CoVar, ContDef)] TermK
  -- let rec fs in e
  | LetFunAbsK [FunDef] TermK

  -- Block terminators
  -- k x..., goto k(x...)
  | JumpK CoVar [TmVar]
  -- f x k, call f(x, k)
  | CallK TmVar [TmVar] [CoValueK]
  -- f @t k
  | InstK TmVar [TypeK] [CoValueK]
  -- if x then k1 else k2
  | IfK TmVar ContDef ContDef
  -- case x : s of c1 -> k1 | c2 -> k2 | ..., branch
  | CaseK TmVar TyConApp [(Ctor, CoValueK)]
  -- halt x
  | HaltK TmVar

-- Hmm. Idle thought:
-- (in the long run) I think I should merge FunDef and AbsDef, using a
-- telescope of parameters for both. This is partly because 'letrec'
-- expressions in 'Source' can contain mixed term and type lambdas, and partly
-- because arity raising/uncurrying may merge together mixed term and type
-- parameters.
--
-- Meanwhile, ContDef can/should have type parameters, then value parameters,
-- akin to GHC's join points.

-- | Parametrized basic blocks, @cont (x:τ)+ => e@.
-- Continuation values do not have names, and therefore cannot be recursive.
-- Let-bound continuations are also non-recursive.
-- (And therefore, inlining them is straightforward)
data ContDef = ContDef [(TmVar, TypeK)] TermK

contDefType :: ContDef -> CoTypeK
contDefType (ContDef xs _) = ContK (map snd xs)

-- | Function definitions: either term functions @f (x:τ) (k:σ) := e@,
-- or type functions @f \@a (k:σ) := e@
data FunDef
  = FunDef TmVar [(TmVar, TypeK)] [(CoVar, CoTypeK)] TermK
  | AbsDef TmVar [(TyVar, KindK)] [(CoVar, CoTypeK)] TermK

funDefName :: FunDef -> TmVar
funDefName (FunDef f _ _ _) = f
funDefName (AbsDef f _ _ _) = f

funDefType :: FunDef -> TypeK
funDefType (FunDef _ xs ks _) = FunK (map snd xs) (map snd ks)
funDefType (AbsDef _ as ks _) = AllK as (map snd ks)

-- | Values require no evaluation.
data ValueK
  = NilK
  | WorldTokenK
  | PairK TmVar TmVar
  | RecordValK [(FieldLabel, TmVar)]
  | IntValK Int
  | BoolValK Bool
  | StringValK String
  | CharValK Char
  | CtorAppK Ctor [TypeK] [TmVar]

data CoValueK
  = CoVarK CoVar
  | ContValK ContDef

data ArithK
  = AddK TmVar TmVar
  | SubK TmVar TmVar
  | MulK TmVar TmVar
  | NegK TmVar

data CmpK
  = CmpEqK TmVar TmVar
  | CmpNeK TmVar TmVar
  | CmpLtK TmVar TmVar
  | CmpLeK TmVar TmVar
  | CmpGtK TmVar TmVar
  | CmpGeK TmVar TmVar
  | CmpEqCharK TmVar TmVar

data StringOpK
  -- x ^ y, concatenation
  = ConcatK TmVar TmVar
  -- char_at_idx x i
  | IndexK TmVar TmVar
  -- string_length x
  | LengthK TmVar

data PrimIO
  = PrimGetLine TmVar
  | PrimPutLine TmVar TmVar

data TypeK
  -- unit
  = UnitK
  -- token#
  | TokenK
  -- int
  | IntK
  -- bool
  | BoolK
  -- string
  | StringK
  -- char
  | CharK
  -- σ × τ
  | ProdK TypeK TypeK
  -- { (l : τ)+ }
  | RecordK [(FieldLabel, TypeK)]
  -- (τ+) => ((σ+) -> !)+
  | FunK [TypeK] [CoTypeK]
  -- forall aa+. ((σ+) -> !)+
  | AllK [(TyVar, KindK)] [CoTypeK]
  -- aa
  | TyVarOccK TyVar
  -- T
  | TyConOccK TyCon
  -- τ σ
  | TyAppK TypeK TypeK

-- | A co-type is the type of a continuation.
-- @(τ+) -> !@
newtype CoTypeK = ContK [TypeK]

data KindK
  = StarK
  | KArrK KindK KindK
  deriving (Eq)

data TyConApp
  = TyConApp TyCon [TypeK]

asTyConApp :: TypeK -> Maybe TyConApp
asTyConApp (TyConOccK tc) = Just (TyConApp tc [])
asTyConApp (TyAppK t s) = go t [s]
  where
    go (TyConOccK tc) acc = Just (TyConApp tc acc)
    go (TyAppK t' s') acc = go t' (s' : acc)
    go _ _ = Nothing
asTyConApp _ = Nothing

fromTyConApp :: TyConApp -> TypeK
fromTyConApp (TyConApp tc args) = foldl TyAppK (TyConOccK tc) args


-- Alpha-Equality of types

-- | Test two types for alpha-equality.
eqTypeK :: TypeK -> TypeK -> Bool
eqTypeK t s = eqTypeK' (Alpha 0 Map.empty Map.empty) t s

-- | Test two co-types for alpha-equality.
eqCoTypeK :: CoTypeK -> CoTypeK -> Bool
eqCoTypeK t s = eqCoTypeK' (Alpha 0 Map.empty Map.empty) t s

eqTypeK' :: Alpha -> TypeK -> TypeK -> Bool
eqTypeK' sc (TyVarOccK aa) (TyVarOccK bb) = varAlpha aa bb sc
eqTypeK' _ (TyVarOccK _) _ = False
eqTypeK' _ (TyConOccK tc1) (TyConOccK tc2) = tc1 == tc2
eqTypeK' _ (TyConOccK _) _ = False
eqTypeK' sc (AllK aas ts) (AllK bbs ss) =
  bindAlpha sc aas bbs $ \sc' -> allEqual (eqCoTypeK' sc') ts ss
eqTypeK' _ (AllK _ _) _ = False
eqTypeK' _ UnitK UnitK = True
eqTypeK' _ UnitK _ = False
eqTypeK' _ TokenK TokenK = True
eqTypeK' _ TokenK _ = False
eqTypeK' _ IntK IntK = True
eqTypeK' _ IntK _ = False
eqTypeK' _ BoolK BoolK = True
eqTypeK' _ BoolK _ = False
eqTypeK' _ StringK StringK = True
eqTypeK' _ StringK _ = False
eqTypeK' _ CharK CharK = True
eqTypeK' _ CharK _ = False
eqTypeK' sc (ProdK t1 s1) (ProdK t2 s2) = eqTypeK' sc t1 t2 && eqTypeK' sc s1 s2
eqTypeK' _ (ProdK _ _) _ = False
eqTypeK' sc (RecordK fs1) (RecordK fs2) = allEqual f fs1 fs2
  where f (f1, t1) (f2, t2) = f1 == f2 && eqTypeK' sc t1 t2
eqTypeK' _ (RecordK _) _ = False
eqTypeK' sc (TyAppK t1 s1) (TyAppK t2 s2) = eqTypeK' sc t1 t2 && eqTypeK' sc s1 s2
eqTypeK' _ (TyAppK _ _) _ = False
eqTypeK' sc (FunK ts1 ss1) (FunK ts2 ss2) =
  allEqual (eqTypeK' sc) ts1 ts2 && allEqual (eqCoTypeK' sc) ss1 ss2
eqTypeK' _ (FunK _ _) _ = False

eqCoTypeK' :: Alpha -> CoTypeK -> CoTypeK -> Bool
eqCoTypeK' sc (ContK ts) (ContK ss) = allEqual (eqTypeK' sc) ts ss

data Alpha = Alpha Int (Map TyVar Int) (Map TyVar Int)

bindAlpha :: Alpha -> [(TyVar, KindK)] -> [(TyVar, KindK)] -> (Alpha -> Bool) -> Bool
bindAlpha sc [] [] k = k sc
bindAlpha sc ((aa, k1):aas) ((bb, k2):bbs) k = k1 == k2 && bindAlpha (bind aa bb sc) aas bbs k
  where
    bind :: TyVar -> TyVar -> Alpha -> Alpha
    bind x y (Alpha l ls rs) = Alpha (l+1) (Map.insert x l ls) (Map.insert y l rs)
-- The lists of bindings had different lengths.
-- Therefore, the types are definitely unequal, and we can short-circuit the
-- computation.
-- (Side note: I think this is analogous to a CPS 'abort' operation, because we
-- directly return a value of the answer type rather than invoke the
-- continuation to obtain one.)
bindAlpha _ _ _ _ = False

varAlpha :: TyVar -> TyVar -> Alpha -> Bool
varAlpha aa bb (Alpha _ ls rs) = case (Map.lookup aa ls, Map.lookup bb rs) of
  (Just la, Just lb) -> la == lb
  (Nothing, Nothing) -> aa == bb
  _ -> False

-- Hmm. This might be 'Eq1.liftEq' in disguise
allEqual :: (a -> a -> Bool) -> [a] -> [a] -> Bool
allEqual _ [] [] = True
allEqual eq (x:xs) (y:ys) = eq x y && allEqual eq xs ys
allEqual _ _ _ = False


-- Free (type) variable traversals

-- | Compute the free type variables of a type.
typeFV :: TypeK -> Set TyVar
typeFV (TyVarOccK aa) = Set.singleton aa
typeFV (AllK aas ss) = Set.unions (map coTypeFV ss) Set.\\ Set.fromList (map fst aas)
typeFV (FunK ts ss) = Set.unions (map typeFV ts) <> Set.unions (map coTypeFV ss)
typeFV (ProdK t s) = typeFV t <> typeFV s
typeFV (RecordK fields) = foldMap (typeFV . snd) fields
typeFV (TyAppK t s) = typeFV t <> typeFV s
typeFV UnitK = Set.empty
typeFV TokenK = Set.empty
typeFV IntK = Set.empty
typeFV BoolK = Set.empty
typeFV StringK = Set.empty
typeFV CharK = Set.empty
typeFV (TyConOccK _) = Set.empty

-- | Compute the free type variables of a co-type.
coTypeFV :: CoTypeK -> Set TyVar
coTypeFV (ContK ts) = Set.unions (map typeFV ts)


-- Capture-Avoiding Substitution

-- | Apply a substitution to a type.
substTypeK :: Subst -> TypeK -> TypeK
substTypeK sub (TyVarOccK aa) = substVar sub aa
substTypeK sub (AllK aas ss) =
  let (sub', aas') = bindSubst sub aas in
  AllK aas' (map (substCoTypeK sub') ss)
substTypeK sub (FunK ts ss) = FunK (map (substTypeK sub) ts) (map (substCoTypeK sub) ss)
substTypeK sub (ProdK t s) = ProdK (substTypeK sub t) (substTypeK sub s)
substTypeK sub (RecordK fields) = RecordK (map (\ (f, t) -> (f, substTypeK sub t)) fields)
substTypeK sub (TyAppK t s) = TyAppK (substTypeK sub t) (substTypeK sub s)
substTypeK _ UnitK = UnitK
substTypeK _ TokenK = TokenK
substTypeK _ IntK = IntK
substTypeK _ BoolK = BoolK
substTypeK _ StringK = StringK
substTypeK _ CharK = CharK
substTypeK _ (TyConOccK tc) = TyConOccK tc

-- | Apply a substitution to a co-type.
substCoTypeK :: Subst -> CoTypeK -> CoTypeK
substCoTypeK sub (ContK ss) = ContK (map (substTypeK sub) ss)

substTyConApp :: Subst -> TyConApp -> TyConApp
substTyConApp sub (TyConApp tc ts) = TyConApp tc (map (substTypeK sub) ts)

data Subst = Subst (Map TyVar TypeK) (Set TyVar)

listSubst :: [(TyVar, TypeK)] -> Subst
listSubst xs = Subst (Map.fromList xs) sc
  where
    -- "Secrets of the GHC Inliner" says that you only need the FTV of the
    -- range of the substitution.
    sc = Set.unions (map (\ (_, t) -> typeFV t) xs)

substVar :: Subst -> TyVar -> TypeK
substVar (Subst sub _) aa = case Map.lookup aa sub of
  Nothing -> TyVarOccK aa
  Just t -> t

bindSubst :: Traversable t => Subst -> t (TyVar, KindK) -> (Subst, t (TyVar, KindK))
bindSubst = mapAccumL bindOne
  where
    bindOne :: Subst -> (TyVar, KindK) -> (Subst, (TyVar, KindK))
    bindOne (Subst s sc) (aa, kk) =
      if Set.member aa sc then
        let bb = freshen sc aa in
        (Subst (Map.insert aa (TyVarOccK bb) s) (Set.insert bb sc), (bb, kk))
      else
        (Subst (Map.delete aa s) (Set.insert aa sc), (aa, kk))

    freshen :: Set TyVar -> TyVar -> TyVar
    freshen sc (TyVar aa i) =
      -- 'freshen' is only called when 'aa' shadows something in scope, so we
      -- always need to increment at least once.
      let bb = TyVar aa (i+1) in
      if Set.member bb sc then freshen sc bb else bb


-- Pretty-printing

indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintProgram :: Program -> String
pprintProgram (Program ds e) = concatMap (pprintDataDecl 0) ds ++ pprintTerm 0 e

pprintDataDecl :: Int -> DataDecl -> String
pprintDataDecl n (DataDecl tc kind ctors) =
  indent n $ "data " ++ show tc ++ " : " ++ pprintKind kind ++ " where\n" ++
  unlines (map (pprintCtorDecl (n+2)) ctors)

pprintCtorDecl :: Int -> CtorDecl -> String
pprintCtorDecl n (CtorDecl c tyargs args) =
  indent n $ show c ++ "(" ++ intercalate ", " (map f tyargs ++ map pprintType args) ++ ")"
  where f (aa, k) = "@" ++ show aa ++ " : " ++ pprintKind k

pprintTerm :: Int -> TermK -> String
pprintTerm n (HaltK x) = indent n $ "halt " ++ show x ++ ";\n"
pprintTerm n (JumpK k xs) = indent n $ show k ++ " " ++ intercalate " " (map show xs) ++ ";\n"
pprintTerm n (CallK f xs ks) =
  indent n $ show f ++ " " ++ intercalate " " (map show xs ++ map pprintCoValue ks) ++ ";\n"
pprintTerm n (InstK f ts ks) =
  indent n $ intercalate " @" (show f : map pprintType ts) ++ " " ++ intercalate " " (map pprintCoValue ks) ++ ";\n"
pprintTerm n (IfK x k1 k2) =
  indent n $ "if " ++ show x ++ " then " ++ pprintContDef k1 ++ " else " ++ pprintContDef k2
pprintTerm n (CaseK x tcapp ks) =
  let branches = intercalate " | " (map pprintBranch ks) in
  let t = fromTyConApp tcapp in
  indent n $ "case " ++ show x ++ " : " ++ pprintType t  ++ " of " ++ branches ++ ";\n"
pprintTerm n (LetValK x t v e) =
  indent n ("let " ++ show x ++ " : " ++ pprintType t ++ " = " ++ pprintValue v ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetFunAbsK fs e) =
  indent n "letfun\n" ++ concatMap (pprintFunDef (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetContK ks e) =
  indent n "letcont\n" ++ concatMap (pprintContBind (n+2)) ks ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetFstK x t y e) =
  indent n ("let " ++ show x ++ " : " ++ pprintType t ++ " = fst " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetSndK x t y e) =
  indent n ("let " ++ show x ++ " : " ++ pprintType t ++ " = snd " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetFieldK x t y f e) =
  indent n ("let " ++ show x ++ " : " ++ pprintType t ++ " = " ++ show y ++ "#" ++ show f ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetArithK x op e) =
  indent n ("let " ++ show x ++ " = " ++ pprintArith op ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetCompareK x op e) =
  indent n ("let " ++ show x ++ " = " ++ pprintCompare op ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetStringOpK x t op e) =
  indent n ("let " ++ show x ++ " : " ++ pprintType t ++ " = " ++ pprintStringOp op ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetBindK x y prim e) =
  indent n ("let " ++ show x ++ ", " ++ show y ++ " = " ++ pprintPrimIO prim ++ ";\n") ++ pprintTerm n e

pprintBranch :: (Ctor, CoValueK) -> String
pprintBranch (c, k) = show c ++ " -> " ++ pprintCoValue k

pprintValue :: ValueK -> String
pprintValue NilK = "()"
pprintValue WorldTokenK = "WORLD#"
pprintValue (PairK x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue (RecordValK []) = "{}"
pprintValue (RecordValK xs) = "{ " ++ intercalate ", " (map pprintField xs) ++ " }"
  where pprintField (f, x) = show f ++ " = " ++ show x
pprintValue (IntValK i) = show i
pprintValue (BoolValK b) = if b then "true" else "false"
pprintValue (StringValK s) = show s
pprintValue (CharValK s) = show s
pprintValue (CtorAppK c tyargs args) = show c ++ "(" ++ intercalate ", @" (map pprintType tyargs) ++ ", " ++ intercalate ", " (map show args) ++ ")"

pprintCoValue :: CoValueK -> String
pprintCoValue (CoVarK k) = show k
pprintCoValue (ContValK cont) = pprintContDef cont

pprintArith :: ArithK -> String
pprintArith (AddK x y) = show x ++ " + " ++ show y
pprintArith (SubK x y) = show x ++ " - " ++ show y
pprintArith (MulK x y) = show x ++ " * " ++ show y
pprintArith (NegK x) = "- " ++ show x

pprintCompare :: CmpK -> String
pprintCompare (CmpEqK x y) = show x ++ " == " ++ show y
pprintCompare (CmpNeK x y) = show x ++ " != " ++ show y
pprintCompare (CmpLtK x y) = show x ++ " < " ++ show y
pprintCompare (CmpLeK x y) = show x ++ " <= " ++ show y
pprintCompare (CmpGtK x y) = show x ++ " > " ++ show y
pprintCompare (CmpGeK x y) = show x ++ " >= " ++ show y
pprintCompare (CmpEqCharK x y) = show x ++ " == " ++ show y

pprintStringOp :: StringOpK -> String
pprintStringOp (ConcatK x y) = show x ++ " ^ " ++ show y
pprintStringOp (IndexK x y) = show x ++ ".char_at_idx " ++ show y
pprintStringOp (LengthK x) = "string_length " ++ show x

pprintPrimIO :: PrimIO -> String
pprintPrimIO (PrimGetLine x) = "getLine " ++ show x
pprintPrimIO (PrimPutLine x y) = "putLine " ++ show x ++ " " ++ show y

pprintFunDef :: Int -> FunDef -> String
pprintFunDef n (FunDef f xs ks e) =
  indent n (show f ++ " " ++ params ++ " =\n") ++ pprintTerm (n+2) e
  where
    -- One parameter list or two?
    params = "(" ++ intercalate ", " (map pprintTmParam xs ++ map pprintCoParam ks) ++ ")"
    pprintTmParam (x, t) = show x ++ " : " ++ pprintType t
    pprintCoParam (k, s) = show k ++ " : " ++ pprintCoType s
pprintFunDef n (AbsDef f as ks e) =
  indent n (show f ++ " " ++ params ++ " =\n") ++ pprintTerm (n+2) e
  where
    -- One parameter list or two?
    params = "(" ++ intercalate ", " (map pprintTyParam as ++ map pprintCoParam ks) ++ ")"
    pprintTyParam (aa, kk) = "@" ++ show aa ++ " :: " ++ pprintKind kk
    pprintCoParam (k, s) = show k ++ " : " ++ pprintCoType s

pprintContDef :: ContDef -> String
-- Hmm. This isn't going to work very well.
-- The body of the continuation will be broken onto new lines.
pprintContDef (ContDef xs e) = "(cont " ++ pprintTmParams xs ++ " => " ++ pprintTerm 0 e ++ ")"

pprintContBind :: Int -> (CoVar, ContDef) -> String
pprintContBind n (k, ContDef xs e) =
  indent n (show k ++ " " ++ pprintTmParams xs ++ " =\n") ++ pprintTerm (n+2) e
  where

pprintTmParams :: [(TmVar, TypeK)] -> String
pprintTmParams xs = "(" ++ intercalate ", " (map f xs) ++ ")"
  where f (x, t) = show x ++ " : " ++ pprintType t

pprintType :: TypeK -> String
pprintType (ProdK t s) = pprintAType t ++ " * " ++ pprintAType s
pprintType (RecordK []) = "{}"
pprintType (RecordK xs) = "{ " ++ intercalate ", " (map pprintField xs) ++ " }"
  where pprintField (f, t) = show f ++ " : " ++ pprintType t
pprintType (FunK ts ss) =
  "(" ++ intercalate ", " tmParams ++ ") -> (" ++ intercalate ", " coParams ++ ")"
  where
    tmParams = map pprintType ts
    coParams = map pprintCoType ss
pprintType IntK = "int"
pprintType UnitK = "unit"
pprintType TokenK = "token"
pprintType BoolK = "bool"
pprintType StringK = "string"
pprintType CharK = "char"
pprintType (TyVarOccK aa) = show aa
pprintType (AllK aas ss) =
  "forall (" ++ intercalate ", " (map f aas) ++ "). (" ++ intercalate ", " (map pprintCoType ss) ++ ") -> 0"
  where f (aa, kk) = show aa ++ " :: " ++ pprintKind kk
pprintType (TyConOccK tc) = show tc
pprintType (TyAppK t1 t2) = pprintType t1 ++ " " ++ pprintType t2

pprintAType :: TypeK -> String
pprintAType (TyVarOccK aa) = show aa
pprintAType IntK = "int"
pprintAType UnitK = "unit"
pprintAType TokenK = "unit"
pprintAType BoolK = "bool"
pprintAType StringK = "string"
pprintAType (RecordK []) = "{}"
pprintAType (RecordK xs) = "{ " ++ intercalate ", " (map pprintField xs) ++ " }"
  where pprintField (f, t) = show f ++ " : " ++ pprintType t
pprintAType t = "(" ++ pprintType t ++ ")"

pprintCoType :: CoTypeK -> String
pprintCoType (ContK ss) = "(" ++ intercalate ", " (map pprintType ss) ++ ") -> 0"

pprintKind :: KindK -> String
pprintKind StarK = "*"
pprintKind (KArrK StarK k2) = "* -> " ++ pprintKind k2
pprintKind (KArrK k1 k2) = "(" ++ pprintKind k1 ++ ") -> " ++ pprintKind k2
