
module Source
  ( Term(..)
  , TmArith(..)
  , TmCmp(..)
  , TmStringOp(..)
  , TmVar(..)
  , TmFun(..)
  , Type(..)
  , TyVar(..)
  , Kind(..)
  , FieldLabel(..)

  , TyConApp(..)
  , asTyConApp
  , fromTyConApp

  , eqType
  , Subst
  , singleSubst
  , makeSubst
  , substType
  , ftv

  , TyCon(..)
  , Ctor(..)
  , Program(..)
  , DataDecl(..)
  , CtorDecl(..)

  , pprintType
  , pprintKind
  ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Bifunctor
import Data.List (intercalate)

-- In the future, it may be worthwhile to do 'Source'-level optimizations.
-- At the very least, arity raising/uncurrying is much easier here.
-- (On a related note, maybe support multiple arguments/parameters here, with
-- requirement of exact arity matching. Parser still generates curried
-- functions and applications, but Source and CPS support the uncurried
-- versions as well.)
--
-- Idea for arity/eta-expansion: that thing with different arrow types for
-- eta-safe and eta-unsafe functions. (and different lambda and application)
-- CPS for an eta-safe function could gather eta-safe lambdas/apps
-- (The parser still only generates eta-unsafe things, annotation pass to
-- convert where possible)
-- (See 'Making a Faster Curry with Extensional Types')
-- (See also 'Kinds are Calling Conventions')

-- TODO: Move Source and TypeCheck to Source.IR and Source.TypeCheck
-- Also, once I have a name resolution and/or elaboration pass, it may make
-- more sense to call this Core instead of Source.

-- | Term variables stand for values.
newtype TmVar = TmVar String
  deriving (Eq, Ord)

instance Show TmVar where
  show (TmVar x) = x

-- | Type variables stand for types.
data TyVar
  = TyVar String
  deriving (Eq, Ord)

instance Show TyVar where
  show (TyVar x) = x


data TyCon = TyCon String
  deriving (Eq, Ord)

instance Show TyCon where
  show (TyCon tc) = tc

data Ctor = Ctor String
  deriving (Eq, Ord)

instance Show Ctor where
  show (Ctor c) = c

newtype FieldLabel = FieldLabel String
  deriving (Eq)

instance Show FieldLabel where
  show (FieldLabel f) = f


data Program = Program [DataDecl] Term


data DataDecl = DataDecl TyCon [(TyVar, Kind)] [CtorDecl]

data CtorDecl = CtorDecl Ctor [Type]


data Term
  -- x
  = TmVarOcc TmVar
  -- \ (x:t) -> e
  | TmLam TmVar Type Term
  -- e1 e2
  | TmApp Term Term
  -- (e1, e2)
  | TmPair Term Term
  -- fst e
  | TmFst Term
  -- snd e
  | TmSnd Term
  -- e #field
  | TmFieldProj Term FieldLabel
  -- { l1 = e1, ..., ln = en }
  | TmRecord [(FieldLabel, Term)]
  -- let x:t = e1 in e2
  | TmLet TmVar Type Term Term
  -- let rec (x:t = e)+ in e'
  | TmLetRec [(TmVar, Type, Term)] Term
  -- ()
  | TmNil
  -- 17
  | TmInt Int
  -- true, false
  | TmBool Bool
  -- if c return s then t else f
  | TmIf Term Type Term Term
  -- e1 `op` e2
  | TmArith Term TmArith Term
  -- - e1
  | TmNegate Term
  -- e1 `cmp` e2
  | TmCmp Term TmCmp Term
  -- \ @(a : k) -> e
  | TmTLam TyVar Kind Term
  -- e @s
  | TmTApp Term Type
  -- "foo"
  | TmString String
  -- 'x'
  | TmChar Char
  -- e1 `stringOp` e2
  | TmStringOp Term TmStringOp Term
  -- c
  | TmCtorOcc Ctor
  -- case e return s of { (c_i (x:t)+ -> e_i')+ }
  | TmCase Term Type [(Ctor, [(TmVar, Type)], Term)]
  -- pure e
  | TmPure Term
  -- let x : t <- e1 in e2
  | TmBind TmVar Type Term Term
  -- getLine
  | TmGetLine
  -- putLine e
  | TmPutLine Term
  -- runIO e
  | TmRunIO Term

data TmArith
  = TmArithAdd
  | TmArithSub
  | TmArithMul

data TmCmp
  = TmCmpEq
  | TmCmpNe
  | TmCmpLt
  | TmCmpLe
  | TmCmpGt
  | TmCmpGe
  | TmCmpEqChar

data TmStringOp
  -- s1 ^ s2
  = TmConcat
  -- char_at_idx x i
  | TmIndexStr

-- | Named function definitions are one way of doing recursion.
-- (On the other hand, let-rec expressions.)
data TmFun
  -- | @f (x : t) : t' = e@
  = TmFun TmVar TmVar Type Type Term
  -- | @f \@a : t' = e@
  | TmTFun TmVar TyVar Kind Type Term

data Type
  = TyUnit
  | TyInt
  | TyBool
  | TyString
  | TyChar
  | TyVarOcc TyVar
  | TyConOcc TyCon
  | TyAll TyVar Kind Type
  | TyProd Type Type
  | TyArr Type Type
  | TyApp Type Type
  | TyRecord [(FieldLabel, Type)]
  | TyIO Type

instance Eq Type where
  (==) = eqType emptyAE

data TyConApp
  = CaseBool
  | TyConApp TyCon [Type]

asTyConApp :: Type -> Maybe TyConApp
asTyConApp TyBool = Just CaseBool
asTyConApp (TyConOcc tc) = Just (TyConApp tc [])
asTyConApp (TyApp t s) = go t [s]
  where
    go (TyApp t' s') args = go t' (s' : args)
    go (TyConOcc tc) args = Just (TyConApp tc args)
    go _ _ = Nothing
asTyConApp _ = Nothing

fromTyConApp :: TyConApp -> Type
fromTyConApp CaseBool = TyBool
fromTyConApp (TyConApp tc tys) = foldl TyApp (TyConOcc tc) tys

data Kind
  = KiStar
  | KiArr Kind Kind
  deriving (Eq)


data AE = AE Int (Map TyVar Int) (Map TyVar Int)

emptyAE :: AE
emptyAE = AE 0 Map.empty Map.empty

lookupAE :: AE -> TyVar -> TyVar -> Bool
lookupAE (AE _ fw bw) x y = case (Map.lookup x fw, Map.lookup y bw) of
  -- Both bound: should be bound at the same level
  (Just xl, Just yl) -> xl == yl
  -- Both free: require exact equality
  (Nothing, Nothing) -> x == y
  -- Cannot be equal if one free but the other is bound
  _ -> False

bindAE :: TyVar -> TyVar -> AE -> AE
bindAE x y (AE l fw bw) = AE (l+1) (Map.insert x l fw) (Map.insert y l bw)

-- | Alpha-equality of two types
eqType :: AE -> Type -> Type -> Bool
eqType ae (TyVarOcc x) (TyVarOcc y) = lookupAE ae x y
eqType _ (TyVarOcc _) _ = False
eqType _ (TyConOcc c1) (TyConOcc c2) = c1 == c2
eqType _ (TyConOcc _) _ = False
eqType _ TyUnit TyUnit = True
eqType _ TyUnit _ = False
eqType _ TyBool TyBool = True
eqType _ TyBool _ = False
eqType _ TyInt TyInt = True
eqType _ TyInt _ = False
eqType _ TyString TyString = True
eqType _ TyString _ = False
eqType _ TyChar TyChar = True
eqType _ TyChar _ = False
eqType ae (TyProd t1 t2) (TyProd t3 t4) = eqType ae t1 t3 && eqType ae t2 t4
eqType _ (TyProd _ _) _ = False
eqType ae (TyRecord fs1) (TyRecord fs2) = go fs1 fs2
  where
    go [] [] = True
    go ((f1, t1):fs1') ((f2, t2):fs2') = f1 == f2 && eqType ae t1 t2 && go fs1' fs2'
    go _ _ = False
eqType _ (TyRecord _) _ = False
eqType ae (TyArr arg1 ret1) (TyArr arg2 ret2) =
  eqType ae arg1 arg2 && eqType ae ret1 ret2
eqType _ (TyArr _ _) _ = False
eqType ae (TyApp arg1 ret1) (TyApp arg2 ret2) =
  eqType ae arg1 arg2 && eqType ae ret1 ret2
eqType _ (TyApp _ _) _ = False
eqType ae (TyIO arg1) (TyIO arg2) =
  eqType ae arg1 arg2
eqType _ (TyIO _) _ = False
eqType ae (TyAll x k1 t) (TyAll y k2 s) = k1 == k2 && eqType (bindAE x y ae) t s
eqType _ (TyAll _ _ _) _ = False


data Subst = Subst { substScope :: Set TyVar, substMapping :: Map TyVar Type }

-- | Construct a singleton substitution, @[aa := t]@.
singleSubst :: TyVar -> Type -> Subst
singleSubst aa t = Subst { substScope = ftv t, substMapping = Map.singleton aa t }

makeSubst :: [(TyVar, Type)] -> Subst
makeSubst binds = Subst { substScope = foldMap (ftv . snd) binds, substMapping = Map.fromList binds }

substBind :: Subst -> TyVar -> (Subst, TyVar)
substBind (Subst sc sub) aa =
  if Set.notMember aa sc then
    (Subst (Set.insert aa sc) (Map.delete aa sub), aa)
  else
    go (0 :: Int)
  where
    go i =
      let TyVar aa' = aa in
      let bb = TyVar (aa' ++ show i) in
      if Set.notMember bb sc then
        (Subst (Set.insert bb sc) (Map.insert aa (TyVarOcc bb) sub), bb)
      else
        go (i+1)

substTyVar :: Subst -> TyVar -> Type
substTyVar sub aa = case Map.lookup aa (substMapping sub) of
  Nothing -> TyVarOcc aa
  Just t -> t

-- | Apply a substitution to a type, @substType sub t' === t'[sub]@.
substType :: Subst -> Type -> Type
substType sub (TyVarOcc bb) = substTyVar sub bb
substType sub (TyAll aa ki t) = let (sub', aa') = substBind sub aa in TyAll aa' ki (substType sub' t)
substType _ TyUnit = TyUnit
substType _ TyBool = TyBool
substType _ TyInt = TyInt
substType _ TyString = TyString
substType _ TyChar = TyChar
substType sub (TyProd t1 t2) = TyProd (substType sub t1) (substType sub t2)
substType sub (TyRecord fs) = TyRecord (map (second (substType sub)) fs)
substType sub (TyArr t1 t2) = TyArr (substType sub t1) (substType sub t2)
substType sub (TyApp t1 t2) = TyApp (substType sub t1) (substType sub t2)
substType sub (TyIO t1) = TyIO (substType sub t1)
substType _ (TyConOcc tc) = TyConOcc tc

-- | Compute the free type variables of a type
ftv :: Type -> Set TyVar
ftv (TyVarOcc aa) = Set.singleton aa
ftv (TyAll bb _ t) = Set.delete bb (ftv t)
ftv (TyProd t1 t2) = ftv t1 <> ftv t2
ftv (TyRecord fs) = foldMap (ftv . snd) fs
ftv (TyArr t1 t2) = ftv t1 <> ftv t2
ftv TyUnit = Set.empty
ftv TyBool = Set.empty
ftv TyInt = Set.empty
ftv TyString = Set.empty
ftv TyChar = Set.empty
ftv (TyConOcc _) = Set.empty
ftv (TyApp t1 t2) = ftv t1 <> ftv t2
ftv (TyIO t1) = ftv t1

-- something something showsPrec
pprintType :: Int -> Type -> String
pprintType _ TyUnit = "unit"
pprintType _ TyBool = "bool"
pprintType _ TyInt = "int"
pprintType _ TyString = "string"
pprintType _ TyChar = "char"
pprintType _ (TyRecord []) = "{}"
pprintType _ (TyRecord fs) = "{ " ++ intercalate ", " (map pprintField fs) ++ " }"
  where pprintField (f, t) = show f ++ " : " ++ pprintType 0 t
-- infixr 4 ->
pprintType p (TyArr t1 t2) = parensIf (p > 4) $ pprintType 5 t1 ++ " -> " ++ pprintType 4 t2
-- infix 5 *
pprintType p (TyProd t1 t2) = parensIf (p > 5) $ pprintType 6 t1 ++ " * " ++ pprintType 6 t2
-- infixl 10 __
pprintType p (TyApp t1 t2) = parensIf (p > 10) $ pprintType 10 t1 ++ " " ++ pprintType 11 t2
pprintType p (TyIO t1) = parensIf (p > 10) $ "IO " ++ pprintType 11 t1
pprintType _ (TyVarOcc x) = show x
pprintType _ (TyConOcc c) = show c
pprintType p (TyAll x ki t) =
  parensIf (p > 0) $ "forall (" ++ show x ++ " : " ++ pprintKind ki ++ "). " ++ pprintType 0 t

-- TODO: Decide textual representation for kind of inhabited types: '*' is
-- ambiguous with product.
pprintKind :: Kind -> String
pprintKind KiStar = "*"
pprintKind (KiArr KiStar k2) = "* -> " ++ pprintKind k2
pprintKind (KiArr k1 k2) = "(" ++ pprintKind k1 ++ ") -> " ++ pprintKind k2

parensIf :: Bool -> String -> String
parensIf True x = "(" ++ x ++ ")"
parensIf False x = x

