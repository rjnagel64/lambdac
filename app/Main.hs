{-# LANGUAGE DataKinds #-}

module Main where

import qualified Source as S
import qualified CPS as K
import qualified CC as C
import qualified Hoist as H
import qualified Emit as E

-- import Experiments.STLC
--
-- e :: Term v 'TyBool
-- e = TmApp (TmLam "x" (\x -> TmVarOcc x)) TmTrue

src :: S.Term
src = S.TmApp (S.TmLam x (S.TmFst (S.TmVarOcc x))) (S.TmPair S.TmNil S.TmNil)
  where x = S.TmVar "x"

main :: IO ()
main = do
  putStrLn "Hello, Haskell!"
  -- putStrLn $ pprintTerm emptyScope $ cpsTerm e

  -- ... Did I never provide a "HALT" continuation?
  let srcK = K.cpsMain src
  let srcC = C.cconv srcK
  let (srcH, decls) = H.runHoist $ H.hoist srcC
  let obj = unlines $ E.emitProgram (decls, srcH)
  putStrLn obj
