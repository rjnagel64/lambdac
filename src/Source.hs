
module Source
  ( Term(..)
  , TmArith(..)
  , TmCmp(..)
  , TmVar(..)
  , TmFun(..)
  , Type(..)
  , TyVar(..)
  , eqType
  , subst
  , ftv
  , pprintType
  ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

-- TODO: 'Source' level optimizations?
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

-- | Term variables stand for values
newtype TmVar = TmVar String
  deriving (Eq, Ord)

instance Show TmVar where
  show (TmVar x) = x

-- | Continuation variables name basic blocks and jump targets.
newtype CoVar = CoVar String
  deriving (Eq, Ord)


data Term
  -- x
  = TmVarOcc TmVar
  -- case e return s of inl (x : t1) -> e1; inr (y : t2) -> e2
  | TmCase Term Type (TmVar, Type, Term) (TmVar, Type, Term)
  -- inl @a @b e
  | TmInl Type Type Term
  -- inr @a @b e
  | TmInr Type Type Term
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
  -- let x:t = e1 in e2
  | TmLet TmVar Type Term Term
  -- let rec fs+ in e
  | TmRecFun [TmFun] Term
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
  -- [] @a
  | TmEmpty Type
  -- x :: xs
  | TmCons Term Term
  -- case uncons e return s of nil -> e1; cons (y : t1) (ys : t2) -> e2
  | TmCaseList Term Type Term ((TmVar, Type), (TmVar, Type), Term)
  | TmTLam TyVar Term
  | TmTApp Term Type

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


-- @f (x : t) : t' = e@, used for recursion.
data TmFun = TmFun TmVar TmVar Type Type Term

data Type
  = TySum Type Type
  | TyProd Type Type
  | TyArr Type Type
  | TyUnit
  | TyInt
  | TyBool
  | TyVarOcc TyVar
  | TyAll TyVar Type
  | TyList Type

data TyVar
  = TyVar String
  deriving (Eq, Ord)

instance Show TyVar where
  show (TyVar x) = x

-- | Alpha-equality of two types
eqType :: Type -> Type -> Bool
eqType = eqType' Map.empty Map.empty

eqType' :: Map TyVar TyVar -> Map TyVar TyVar -> Type -> Type -> Bool
eqType' fw bw (TyVarOcc x) (TyVarOcc y) = case (Map.lookup x fw, Map.lookup y bw) of
  -- Both bound: check that bijection holds
  (Just y', Just x') -> y' == y && x' == x
  -- Both free: require exact equality
  (Nothing, Nothing) -> x == y
  -- Cannot be equal if one free but the other is bound
  _ -> False
eqType' _ _ (TyVarOcc _) _ = False
eqType' _ _ TyUnit TyUnit = True
eqType' _ _ TyUnit _ = False
eqType' _ _ TyBool TyBool = True
eqType' _ _ TyBool _ = False
eqType' _ _ TyInt TyInt = True
eqType' _ _ TyInt _ = False
eqType' fw bw (TyProd t1 t2) (TyProd t3 t4) = eqType' fw bw t1 t3 && eqType' fw bw t2 t4
eqType' _ _ (TyProd _ _) _ = False
eqType' fw bw (TySum t1 t2) (TySum t3 t4) = eqType' fw bw t1 t3 && eqType' fw bw t2 t4
eqType' _ _ (TySum _ _) _ = False
eqType' fw bw (TyArr arg1 ret1) (TyArr arg2 ret2) =
  eqType' fw bw arg1 arg2 && eqType' fw bw ret1 ret2
eqType' _ _ (TyArr _ _) _ = False
eqType' fw bw (TyAll x t) (TyAll y s) = eqType' (Map.insert x y fw) (Map.insert y x bw) t s
eqType' _ _ (TyAll _ _) _ = False
eqType' fw bw (TyList a) (TyList b) = eqType' fw bw a b
eqType' _ _ (TyList _) _ = False

-- | Perform a substitution, @subst aa t t' === t'[aa := t]@.
subst :: TyVar -> Type -> Type -> Type
subst aa t (TyVarOcc bb) = if aa == bb then t else TyVarOcc bb
subst aa t (TyAll bb t') =
  if aa == bb then TyAll bb t' else TyAll bb' (subst aa t (subst bb (TyVarOcc bb') t'))
  where
    vs = ftv t' <> ftv t
    bb' = let TyVar x = bb in go x (0 :: Int)
    go x i = let cc = TyVar (x ++ show i) in if Set.member cc vs then go x (i+1) else cc
subst aa t (TyList t') = TyList (subst aa t t')
subst aa t (TySum t1 t2) = TySum (subst aa t t1) (subst aa t t2)
subst aa t (TyProd t1 t2) = TyProd (subst aa t t1) (subst aa t t2)
subst aa t (TyArr t1 t2) = TyArr (subst aa t t1) (subst aa t t2)
subst _ _ TyUnit = TyUnit
subst _ _ TyBool = TyBool
subst _ _ TyInt = TyInt

-- | Compute the free type variables of a type
ftv :: Type -> Set TyVar
ftv (TyVarOcc aa) = Set.singleton aa
ftv (TyAll bb t) = Set.delete bb (ftv t)
ftv (TySum t1 t2) = ftv t1 <> ftv t2
ftv (TyProd t1 t2) = ftv t1 <> ftv t2
ftv (TyArr t1 t2) = ftv t1 <> ftv t2
ftv TyUnit = Set.empty
ftv TyBool = Set.empty
ftv TyInt = Set.empty
ftv (TyList t) = ftv t
-- something something showsPrec
pprintType :: Int -> Type -> String
pprintType _ TyUnit = "unit"
pprintType _ TyBool = "bool"
pprintType _ TyInt = "int"
-- infixr 4 ->
pprintType p (TyArr t1 t2) = parensIf (p > 4) $ pprintType 5 t1 ++ " -> " ++ pprintType 4 t2
-- infix 5 *
pprintType p (TyProd t1 t2) = parensIf (p > 5) $ pprintType 6 t1 ++ " * " ++ pprintType 6 t2
-- infix 5 +
pprintType p (TySum t1 t2) = parensIf (p > 5) $ pprintType 6 t1 ++ " + " ++ pprintType 6 t2
pprintType _ (TyVarOcc x) = show x
pprintType p (TyAll x t) = parensIf (p > 0) $ "forall " ++ show x ++ "." ++ pprintType 0 t
pprintType p (TyList t) = parensIf (p > 7) $ "list " ++ pprintType 8 t

parensIf :: Bool -> String -> String
parensIf True x = "(" ++ x ++ ")"
parensIf False x = x

