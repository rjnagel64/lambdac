{-# LANGUAGE
    StandaloneDeriving
  , DerivingStrategies
  , GeneralizedNewtypeDeriving
  , MultiParamTypeClasses
  , FlexibleInstances
  #-}

module Hoist () where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Control.Monad.Reader
import Control.Monad.Writer

import Data.Int
import Data.Traversable (for)

import qualified CC as C
import CC (TermC(..))

data CName = LocalCName LocalName | EnvCName EnvName
  deriving (Eq, Ord)
-- TODO: Variable sorts should really be more associated with binding site
-- rather than all uses. (e.g., field types in the environment, obvious from
-- tm/co/fn binder, etc.)
data LocalName = LocalName CSort String
  deriving (Eq, Ord)
data EnvName = EnvName CSort String
  deriving (Eq, Ord)
data CSort = CFun | CCont | CValue
  deriving (Eq, Ord)

data TermH
  = LetValH LocalName ValueH TermH
  | LetPrimH LocalName PrimOp TermH
  -- fst and snd are built-in constructs, for when I expand to n-ary products
  -- and projections.
  | LetFstH LocalName CName TermH
  | JumpH CName CName
  | CallH CName CName CName
  | CaseH CName CName CName
  -- Function and continuation closures may be mutually recursive.
  | AllocFun [FunAlloc] TermH
  | AllocCont [ContAlloc] TermH

data ValueH
  = IntValH Int32

data PrimOp
  = PrimAddInt32 CName CName
  | PrimSubInt32 CName CName
  | PrimMulInt32 CName CName

data FunAlloc
  = FunAlloc LocalName CapturedVars

data ContAlloc
  = ContAlloc LocalName CapturedVars

data CapturedVars = CapturedVars [EnvName] [LocalName]
-- data CapturedVars = CapturedVars [(Name, Sort)] [(Name, Sort)]?

data TopDecl
  = TopFun [FunDecl]
  | TopCont [ContDecl]

data FunDecl
  -- TODO: Include or compute number of required local slots
  = FunDecl CName CapturedVars CName CName TermH

data ContDecl
  -- TODO: Include or compute number of required local slots
  = ContDecl CName CapturedVars CName TermH


-- TODO: Finding the in-scope set could be easier if I maintained a 'Set CName'.
data HoistEnv = HoistEnv (Map C.Name CName)

inScopeSet :: HoistM (Set CName)
inScopeSet = do
  HoistEnv xs <- ask
  pure $ Set.fromList $ map snd $ Map.toList xs

newtype HoistM a = HoistM { runHoistM :: ReaderT HoistEnv (Writer [TopDecl]) a }

deriving newtype instance Functor HoistM
deriving newtype instance Applicative HoistM
deriving newtype instance Monad HoistM
deriving newtype instance MonadReader HoistEnv HoistM
deriving newtype instance MonadWriter [TopDecl] HoistM

-- | After closure conversion, the code for each function and continuation can
-- be lifted to the top level. Additionally, map value, continuation, and
-- function names to C names.
--
-- Return a list of bind groups.
--
-- (Hmm. This is a bottom-up traversal, I think.)
-- TODO: I need to make sure function and continuation names are globally
-- unique, so I can hoist them without conflicts.
hoist :: TermC -> HoistM TermH
hoist (LetFstC x y e) = do
  y' <- hoistVarOcc y
  (x', e') <- withPlace x $ hoist e
  pure (LetFstH x' y' e')
hoist (LetFunC fs e) = do
  e' <- hoist e
  (fs', ds') <- fmap unzip $ for fs $ \ (C.ClosureDef f free rec x k body) -> do
    f' <- pure f -- occurrence or binder?
    let fa = FunAlloc f' _
    body' <- hoist body -- Extend env with free', rec', x, k.
    let fd = FunDecl f _ x k body'
    pure (fa, fd)
  tell [TopFun ds'] -- TODO: This may be in the wrong order. If so, use 'Dual [TopDecl]'
  pure (AllocFun fs' e')

hoistVarOcc :: C.Name -> HoistM CName
hoistVarOcc x = do
  HoistEnv ns <- ask
  pure (ns Map.! x)

withPlace :: C.Name -> HoistM a -> HoistM (LocalName, a)
withPlace x m = do
  x' <- makePlace x
  a <- local (f x') m
  pure (x', a)
  where
    f :: LocalName -> HoistEnv -> HoistEnv
    f x' (HoistEnv ns) = HoistEnv (Map.insert x (LocalCName x') ns)

makePlace :: C.Name -> HoistM LocalName
makePlace (C.Name x) = do
  go x (0 :: Int) <$> inScopeSet
  where
    go x i iss =
      let v = (LocalName CValue (x ++ show i)) in
      -- I think this is fine. We might shadow local names, which is bad, but
      -- environment references are guarded by 'env->'.
      if Set.member (LocalCName v) iss then go x (i+1) iss else v

