
module Source
  ( Term(..)
  , TmArith(..)
  , TmCmp(..)
  , TmVar(..)
  , TmFun(..)
  , Type(..)
  , TyVar(..)
  , pprintType
  ) where

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

-- TODO: Implement lists

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

-- something something showsPrec
pprintType :: Int -> Type -> String
pprintType p TyUnit = "unit"
pprintType p TyBool = "bool"
pprintType p TyInt = "int"
-- infixr 4 ->
pprintType p (TyArr t1 t2) = parensIf (p > 4) $ pprintType 5 t1 ++ " -> " ++ pprintType 4 t2
-- infix 5 *
pprintType p (TyProd t1 t2) = parensIf (p > 5) $ pprintType 6 t1 ++ " * " ++ pprintType 6 t2
-- infix 5 +
pprintType p (TySum t1 t2) = parensIf (p > 5) $ pprintType 6 t1 ++ " + " ++ pprintType 6 t2
pprintType p (TyVarOcc x) = show x
pprintType p (TyAll x t) = parensIf (p > 0) $ "forall " ++ show x ++ "." ++ pprintType 0 t
pprintType p (TyList t) = parensIf (p > 7) $ "List " ++ pprintType 8 t

parensIf :: Bool -> String -> String
parensIf True x = "(" ++ x ++ ")"
parensIf False x = x

