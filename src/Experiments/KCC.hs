{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Experiments.KCC where

import Control.Monad.State
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List (intercalate)

-- An experimental VM based on "Kinds Are Calling Conventions"
-- This may be a viable way to implement (e.g.) an interpreter, or an alternate
-- compilation backend, or something.
--
-- I quite like how it natively supports unboxed types and thunks/strict evaluation.


-- Mostly based on Figure 5: Syntax and Semantics of \cal{ML}

data PrimRep = PtrRep | IntRep
  deriving Show

data Strictness = L | U
  deriving Show

data KnownCC = Eval Strictness | Call [PrimRep]

data Expr
  = PassiveE Passive
  | AppE Passive [Arg]
  | FullAppE Expr [Arg]
  | IntCaseE Expr Var Expr
  | LetE (Var, PrimRep) Strictness Expr Expr

-- A reference is something that can be stored on the heap.
-- This includes boxed integers, closures, and functions.
data Reference
  = IntBoxR Arg
  | ClosR Int Passive
  | LamR [(Var, PrimRep)] Expr

-- I think Value may be a subgrammar of ??Expr?? ???
data Value
  = ConstV Constant
  | IntBoxV Arg
  | ClosV Int Passive

isValue :: Expr -> Maybe Value
isValue (PassiveE (ConstP c)) = Just (ConstV c)
isValue (PassiveE (RefP (IntBoxR a))) = Just (IntBoxV a)
isValue (PassiveE (RefP (ClosR n p))) = Just (ClosV n p)
isValue (PassiveE (RefP (LamR _xs _e))) = Nothing -- why?
isValue (PassiveE (VarP (_x, _pi))) = Nothing -- because variable can lookup in heap
isValue _ = Nothing -- Everything else should rewrite.

-- "A passive expression, which is either a value V or a variable"
data Passive
  = RefP Reference
  | VarP (Var, PrimRep)
  -- This clause is missing from the rules. However, without it, things don't
  -- make a lot of sense.
  -- In particular, the compilation scheme which maps IL.Passive to ML.Passive
  -- needs to translate constants to constants.
  -- Also, without this constructor, the rule [Move] makes no sense.
  | ConstP Constant

-- data Passive
--   = ValP Value
--   | VarP (Var, PrimRep)

data Arg
  = ConstArg Constant
  | VarArg (Var, PrimRep)

data StackCont
  = EmptyK
  | AppK [Arg] StackCont
  | IntCaseK Var Expr StackCont
  | LetK (Var, PrimRep) Expr StackCont
  | SetK Var StackCont

-- data Store
--   = EmptyH
--   | ExtendH Var Reference Store
--   | ExtendMemoH Var Expr Store
-- It would be a *lot* better to just have @Map Var (Either Reference Expr)@ or something.
-- Easier to lookup, easier to update.

data StoreCell = StoreRef Reference | StoreMemo Expr
type Store = Map Var StoreCell

data MachineState = MachineState Expr StackCont Store


-- From Figure 1
data Constant = ConstInt Int | ConstPrim PrimOp
data PrimOp = PrimError | PrimPlus

data Var = Var String
  deriving (Eq, Ord)

instance Show Var where
  show (Var x) = x



data Answer = Answer Value () Store

-- Effect isn't really a good name.
-- FreshName could probably be better integrated/fused.
data Effect
  = Halt Answer
  | HaltError Int
  | Step MachineState
  | FreshName () (Var -> Effect)

run :: Effect -> Either Int Answer
run m = flip evalState 0 $ runM m

runM :: Effect -> State Int (Either Int Answer)
runM (Halt a) = pure (Right a) -- If expr is value and kont is empty, or state is error, return
runM (HaltError n) = pure (Left n)
runM (Step m) = runM (step m)
runM (FreshName () k) = do
  i <- get
  modify' (+ 1)
  let x = Var ("$" ++ show i)
  runM (k x)

step :: MachineState -> Effect
-- Rule [PshApp]
step (MachineState (FullAppE e args) k h) = Step $ MachineState e (AppK args k) h
-- Rule [PshCase]
step (MachineState (IntCaseE e x e') k h) = Step $ MachineState e (IntCaseK x e' k) h
-- Rule [PshLet]
step (MachineState (LetE (x, pi) U e e') k h) = Step $ MachineState e (LetK (x, pi) e' k) h
-- Rule [LAlloc]
step (MachineState (LetE (x, PtrRep) L e e') k h) =
  FreshName () $ \y ->
    let sub = makeSubst [(x, PtrRep)] [VarArg (y, PtrRep)] in
    Step $ MachineState (subst sub e') k (extendMemo y e h)
step (MachineState (LetE (_, IntRep) L _ _) _ _) = error "panic: cannot have lifted machine integer"

-- Rule [Call]
step (MachineState (AppE (RefP (LamR params body)) args) k h) = Step $ MachineState (subst sub body) k h
  where sub = makeSubst params args
-- Rule [Apply]
step (MachineState (PassiveE (RefP (ClosR n p))) (AppK as k) h) =
  if n == length as then
    Step $ MachineState (AppE p as) k h
  else
    error "arity mismatch: IDK"
-- Rule [Unbox]
step (MachineState (PassiveE (RefP (IntBoxR a))) (IntCaseK x e k) h) = Step $ MachineState (subst sub e) k h
  where sub = makeSubst [(x, IntRep)] [a]
-- Rule [Move]
step (MachineState (PassiveE (ConstP c)) (LetK (x, pi) e k) h) = Step $ MachineState (subst sub e) k h
  where sub = makeSubst [(x, pi)] [ConstArg c]
-- Rule [SAlloc]
step (MachineState (PassiveE (RefP r)) (LetK (x, PtrRep) e k) h) =
  FreshName () $ \y ->
    let sub = makeSubst [(x, PtrRep)] [VarArg (y, PtrRep)] in
    Step $ MachineState (subst sub e) k (extendRef y r h)

-- Rule [Fun]
step (MachineState (AppE (VarP (y, PtrRep)) as) k h) = case lookupHeap y h of
  NotFound -> error "panic: missing variable"
  FoundRef r -> Step $ MachineState (AppE (RefP r) as) k h
  FoundMemo e -> error "panic: fn is not evaluated yet?"
-- Rule [Look]
-- Rule [Force]
step (MachineState (PassiveE (VarP (y, PtrRep))) k h) = case lookupHeap y h of
  NotFound -> error "panic: missing variable"
  FoundRef r -> Step $ MachineState (PassiveE (RefP r)) k h
  FoundMemo e -> Step $ MachineState e (SetK y k) h
-- Rule [Memo]
step (MachineState (PassiveE (RefP r)) (SetK y k) h) =
  Step $ MachineState (PassiveE (RefP r)) k (extendRef y r h)

-- Rule [Error]
step (MachineState (AppE (ConstP (ConstPrim PrimError)) [ConstArg (ConstInt n)]) k h) =
  HaltError n

-- Hmm. Can easily end up in a situation with <plus#(x:IntRep, 1) | K | H[x := 17]>
-- 'x' is (conceptually) stored in an integer register, so we should be able to reduce here.
-- The paper omits rules for primitives, though.
step (MachineState (AppE (ConstP (ConstPrim PrimPlus)) [ConstArg (ConstInt m), ConstArg (ConstInt n)]) k h) =
  Step $ MachineState (PassiveE (ConstP (ConstInt (m + n)))) k h

step (MachineState e EmptyK h) = case isValue e of
  Just v -> Halt $ Answer v () h
  Nothing -> error ("Empty continuation stack but not a value: <" ++ ppExpr e ++ " | . | " ++ ppStore h ++ ">")

step (MachineState e k h) = error $ "unhandled case: <" ++ ppExpr e ++ " | " ++ ppStackCont k ++ " | " ++ ppStore h ++ ">"



data Lookup
  = NotFound
  | FoundRef Reference
  | FoundMemo Expr

lookupHeap :: Var -> Store -> Lookup
lookupHeap y h = case Map.lookup y h of
  Nothing -> NotFound
  Just (StoreRef r) -> FoundRef r
  Just (StoreMemo e) -> FoundMemo e

extendRef :: Var -> Reference -> Store -> Store
extendRef y r h = Map.insert y (StoreRef r) h

extendMemo :: Var -> Expr -> Store -> Store
extendMemo y e h = Map.insert y (StoreMemo e) h

data Subst = Subst { substScope :: Set Var, substMapping :: Map Var Arg }

subst :: Subst -> Expr -> Expr
subst sub (PassiveE p) = PassiveE (substPassive sub p)
subst sub (AppE p as) = AppE (substPassive sub p) (substArgList sub as)
subst sub (FullAppE e as) = FullAppE (subst sub e) (substArgList sub as)
subst sub (IntCaseE e x e') =
  let ((x', _), sub') = substBind (x, IntRep) sub in
  IntCaseE (subst sub e) x' (subst sub' e)
subst sub (LetE (x, pi) psi e e') =
  let (x', sub') = substBind (x, pi) sub in
  LetE x' psi (subst sub e) (subst sub' e)

substPassive :: Subst -> Passive -> Passive
substPassive sub (RefP r) = RefP (substReference sub r)
substPassive sub (VarP (x, pi)) = case substVar sub (x, pi) of
  ConstArg c -> ConstP c
  VarArg (y, pi') -> VarP (y, pi')
substPassive sub (ConstP c) = ConstP c

substReference :: Subst -> Reference -> Reference
substReference sub (IntBoxR a) = IntBoxR (substArg sub a)
substReference sub (ClosR n p) = ClosR n (substPassive sub p)
substReference sub (LamR xs e) =
  let (xs', sub') = substBinds xs sub in
  LamR xs' (subst sub' e)

substArgList :: Subst -> [Arg] -> [Arg]
substArgList sub args = map (substArg sub) args

substArg :: Subst -> Arg -> Arg
substArg sub (ConstArg c) = ConstArg c
substArg sub (VarArg (x, pi)) = substVar sub (x, pi)

substVar :: Subst -> (Var, PrimRep) -> Arg
substVar (Subst sc sub) (x, pi) = case Map.lookup x sub of
  Nothing -> VarArg (x, pi)
  Just a -> a

substBind :: (Var, PrimRep) -> Subst -> ((Var, PrimRep), Subst)
substBind (x, pi) (Subst sc sub) =
  if Set.notMember x sc then
    ((x, pi), Subst (Set.insert x sc) (Map.delete x sub))
  else
    go (0 :: Int)
  where
    go i =
      let Var x' = x in
      let y = Var (x' ++ show i) in
      if Set.notMember y sc then
        ((y, pi), Subst (Set.insert y sc) (Map.insert x (VarArg (y, pi)) sub))
      else
        go (i + 1)

substBinds :: Traversable t => t (Var, PrimRep) -> Subst -> (t (Var, PrimRep), Subst)
substBinds xs sub = flip runState sub $ traverse (state . substBind) xs

makeSubst :: [(Var, PrimRep)] -> [Arg] -> Subst
makeSubst xs as =
  if length xs /= length as then
    error "panic: substitution arity mismatch"
  else
    Subst sc sub
  where
    sc = foldMap fv as
    fv (ConstArg _) = Set.empty
    fv (VarArg (x, _)) = Set.singleton x
    sub = Map.fromList $ zipWith (\ (x, pi) a -> (x, a)) xs as



-- Example of reduction steps:
-- (It would be great if I could implement this test case and check that things
-- work.)
--
-- < let[U] z_PtrRep = I# 17 in (λ(x_PtrRep).x_PtrRep) (z_PtrRep) | . | . >
-- ==> [PshLet]
-- < I# 17 | let[U] z_PtrRep in (λ(x_PtrRep).x_PtrRep) (z_PtrRep) | . >
-- ==> [SAlloc]
-- < (λ(x_PtrRep).x_PtrRep) (y_PtrRep) | . | y := I# 17, . >
-- ==> [Call]
-- < y_PtrRep | . | y := I# 17, . >
-- ==> [Look]
-- < I# 17 | . | y := I# 17, . >
-- =/=> .
-- V := (I# 17)
-- H := (y := I# 17, .)
testExpr :: Expr
testExpr =
  LetE (Var "z", PtrRep) U
    (PassiveE (RefP (IntBoxR (ConstArg (ConstInt 17)))))
    (AppE (RefP (LamR [(Var "x", PtrRep)] (PassiveE (VarP (Var "x", PtrRep))))) [VarArg (Var "z", PtrRep)])

testExpr2 :: Expr
testExpr2 =
  LetE (Var "z", PtrRep) U
    (PassiveE (RefP (IntBoxR (ConstArg (ConstInt 17)))))
    (AppE (RefP (LamR [(Var "x", PtrRep)] (AppE (ConstP (ConstPrim PrimPlus)) [VarArg (Var "x", PtrRep), ConstArg (ConstInt 1)]))) [VarArg (Var "z", PtrRep)])


ppAnswer :: Answer -> String
ppAnswer (Answer v () h) = "Result: " ++ ppValue v ++ "\nStore: " ++ ppStore h

ppValue :: Value -> String
ppValue (ConstV c) = ppConstant c
ppValue (IntBoxV a) = "I# " ++ ppArg a
ppValue (ClosV n p) = "Clos[" ++ show n ++ "] " ++ ppPassive p

ppConstant :: Constant -> String
ppConstant (ConstInt i) = show i ++ "#"
ppConstant (ConstPrim p) = ppPrimop p

ppPrimop :: PrimOp -> String
ppPrimop PrimPlus = "plus#"
ppPrimop PrimError = "error#"

ppStore :: Store -> String
ppStore h = intercalate ", " $ map f $ Map.toList h
  where
    f (x, StoreRef r) = show x ++ " := " ++ ppReference r
    f (x, StoreMemo e) = show x ++ " := memo " ++ ppExpr e

ppReference :: Reference -> String
ppReference (IntBoxR a) = "I# " ++ ppArg a
ppReference (ClosR n p) = "Clos[" ++ show n ++ "] " ++ ppPassive p
ppReference (LamR xs e) = "λ (" ++ intercalate ", " (map ppVar xs) ++ "). " ++ ppExpr e

ppExpr :: Expr -> String
ppExpr (PassiveE p) = ppPassive p
ppExpr (AppE p as) = ppPassive p ++ "(" ++ intercalate ", " (map ppArg as) ++ ")"
ppExpr (FullAppE e as) = "(" ++ ppExpr e ++ ") (" ++ intercalate ", " (map ppArg as) ++ ")"
ppExpr (IntCaseE e1 x e2) = "case " ++ ppExpr e1 ++ " of { I# " ++ show x ++ " -> " ++ ppExpr e2 ++ " }"
ppExpr (LetE x lu e1 e2) = "let[" ++ show lu ++ "] " ++ show x ++ " = " ++ ppExpr e1 ++ " in " ++ ppExpr e2

ppPassive :: Passive -> String
ppPassive (RefP r) = ppReference r
ppPassive (VarP x) = ppVar x
ppPassive (ConstP c) = ppConstant c

ppArg :: Arg -> String
ppArg (ConstArg c) = ppConstant c
ppArg (VarArg x) = ppVar x 

ppVar :: (Var, PrimRep) -> String
ppVar (x, pi) = show x ++ ":" ++ show pi

ppStackCont :: StackCont -> String
ppStackCont EmptyK = " ."
ppStackCont (AppK as k) = "[] (" ++ intercalate ", " (map ppArg as) ++ ") ; " ++ ppStackCont k
ppStackCont (IntCaseK x e2 k) = "case [] of { I# " ++ show x ++ " -> " ++ ppExpr e2 ++ "} ; " ++ ppStackCont k
ppStackCont (LetK x e k) = "let " ++ ppVar x ++ " = [] in " ++ ppExpr e ++ " ; " ++ ppStackCont k
ppStackCont (SetK y k) = "set " ++ show y ++ " ; " ++ ppStackCont k


evalExpr :: Expr -> Either Int Answer
evalExpr e = run $ Step (MachineState e EmptyK Map.empty)

main :: IO ()
main = do
  putStrLn "Hello, World!"
  -- putStrLn $ ppAnswer $ evalExpr testExpr
  putStrLn $ either (\n -> "Error: " ++ show n) ppAnswer $ evalExpr testExpr2
