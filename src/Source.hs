
module Source
  ( Term(..)
  , TmArith(..)
  , TmCmp(..)
  , TmVar(..)
  , TmFun(..)
  , Type(..)
  , TyVar(..)

  , eqType
  , Subst
  , singleSubst
  , substType
  , ftv

  , pprintType
  ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

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

-- | Term variables stand for values
newtype TmVar = TmVar String
  deriving (Eq, Ord)

instance Show TmVar where
  show (TmVar x) = x


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
  -- \ @a -> e
  | TmTLam TyVar Term
  -- e @s
  | TmTApp Term Type
  -- "foo"
  | TmString String
  -- s1 ^ s2
  | TmConcat Term Term

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

-- | Named function definitions are one way of doing recursion.
-- (On the other hand, let-rec expressions.)
data TmFun
  -- | @f (x : t) : t' = e@
  = TmFun TmVar TmVar Type Type Term
  -- | @f \@a : t' = e@
  | TmTFun TmVar TyVar Type Term

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
  | TyString

data TyVar
  = TyVar String
  deriving (Eq, Ord)

instance Show TyVar where
  show (TyVar x) = x

-- | Alpha-equality of two types
eqType :: Type -> Type -> Bool
eqType = eqType' 0 Map.empty Map.empty

eqType' :: Int -> Map TyVar Int -> Map TyVar Int -> Type -> Type -> Bool
eqType' _ fw bw (TyVarOcc x) (TyVarOcc y) = case (Map.lookup x fw, Map.lookup y bw) of
  -- Both bound: should be bound at the same level
  (Just xl, Just yl) -> xl == yl
  -- Both free: require exact equality
  (Nothing, Nothing) -> x == y
  -- Cannot be equal if one free but the other is bound
  _ -> False
eqType' _ _ _ (TyVarOcc _) _ = False
eqType' _ _ _ TyUnit TyUnit = True
eqType' _ _ _ TyUnit _ = False
eqType' _ _ _ TyBool TyBool = True
eqType' _ _ _ TyBool _ = False
eqType' _ _ _ TyInt TyInt = True
eqType' _ _ _ TyInt _ = False
eqType' _ _ _ TyString TyString = True
eqType' _ _ _ TyString _ = False
eqType' l fw bw (TyProd t1 t2) (TyProd t3 t4) = eqType' l fw bw t1 t3 && eqType' l fw bw t2 t4
eqType' _ _ _ (TyProd _ _) _ = False
eqType' l fw bw (TySum t1 t2) (TySum t3 t4) = eqType' l fw bw t1 t3 && eqType' l fw bw t2 t4
eqType' _ _ _ (TySum _ _) _ = False
eqType' l fw bw (TyArr arg1 ret1) (TyArr arg2 ret2) =
  eqType' l fw bw arg1 arg2 && eqType' l fw bw ret1 ret2
eqType' _ _ _ (TyArr _ _) _ = False
eqType' l fw bw (TyAll x t) (TyAll y s) = eqType' (l+1) (Map.insert x l fw) (Map.insert y l bw) t s
eqType' _ _ _ (TyAll _ _) _ = False
eqType' l fw bw (TyList a) (TyList b) = eqType' l fw bw a b
eqType' _ _ _ (TyList _) _ = False


data Subst = Subst { substScope :: Set TyVar, substMapping :: Map TyVar Type }

-- | Construct a singleton substitution, @[aa := t]@.
singleSubst :: TyVar -> Type -> Subst
singleSubst aa t = Subst { substScope = ftv t, substMapping = Map.singleton aa t }

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
substType sub (TyAll aa t) = let (sub', aa') = substBind sub aa in TyAll aa' (substType sub' t)
substType _ TyUnit = TyUnit
substType _ TyBool = TyBool
substType _ TyInt = TyInt
substType _ TyString = TyString
substType sub (TyList t) = TyList (substType sub t)
substType sub (TyProd t1 t2) = TyProd (substType sub t1) (substType sub t2)
substType sub (TySum t1 t2) = TySum (substType sub t1) (substType sub t2)
substType sub (TyArr t1 t2) = TyArr (substType sub t1) (substType sub t2)

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
ftv TyString = Set.empty
ftv (TyList t) = ftv t

-- something something showsPrec
pprintType :: Int -> Type -> String
pprintType _ TyUnit = "unit"
pprintType _ TyBool = "bool"
pprintType _ TyInt = "int"
pprintType _ TyString = "string"
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

