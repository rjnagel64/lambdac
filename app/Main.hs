{-# LANGUAGE DataKinds #-}

module Main where

import qualified Source as S
import qualified CPS as K
import qualified CC as C
import qualified Hoist as H
import qualified Emit as E

src :: S.Term
src = S.TmApp (S.TmLam x (S.TmFst (S.TmVarOcc x))) (S.TmPair S.TmNil S.TmNil)
  where x = S.TmVar "x"

main :: IO ()
main = do
  putStrLn "Hello, Haskell!"

  putStrLn $ "--- CPS Transform ---"
  let srcK = K.cpsMain src
  putStrLn $ K.pprintTerm 0 srcK

  putStrLn $ "--- Closure Conversion ---"
  let srcC = C.cconv srcK
  putStrLn $ C.pprintTerm 0 srcC

  putStrLn $ "--- Hoisting ---"
  let (srcH, decls) = H.runHoist $ H.hoist srcC
  putStrLn $ concatMap H.pprintTop decls ++ H.pprintTerm 0 srcH

  putStrLn $ "--- Code Generation ---"
  let obj = unlines $ E.emitProgram (decls, srcH)
  putStrLn obj

  -- TODO: Name output file based on input file
  -- TODO: Generate Makefile fragment?
  writeFile "out.c" obj
