{-# LANGUAGE DataKinds #-}

module Main where

import qualified Source as S
import qualified CPS as K
import qualified CC as C
import qualified Hoist as H
import qualified Emit as E

-- src :: S.Term
-- src = S.TmApp (S.TmLam x (S.TmFst (S.TmVarOcc x))) (S.TmPair (S.TmInt 17) (S.TmInt 32))
--   where x = S.TmVar "x"

-- TODO: A native string type, probably like 'Text' not [Char]?

src :: S.Term
src = S.TmCase (S.TmInr (S.TmInt 33)) x (S.TmAdd (S.TmVarOcc x) (S.TmInt 1)) y (S.TmAdd (S.TmVarOcc y) (S.TmInt (-3)))
  where
    x = S.TmVar "x"
    y = S.TmVar "y"

-- TODO: case isZero x of inl _ ->  31; inr _ -> 19
-- TODO: case isZero x of inl _ -> 31; inr _ -> x + x
-- TODO: case inr 33 of inl x -> x + 1; inr y -> y - 3
--
-- pred :: Int -> Either () Int?

-- Note: Returning multiple values from a function is passing multiple values
-- to the continuation.

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
  -- TODO: Generate Makefile fragment? Yes. Gen-C each module, Gen-makefile, make -f $exe.make $exe
  writeFile "out.c" obj
