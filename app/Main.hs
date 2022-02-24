{-# LANGUAGE DataKinds #-}

module Main where

import System.Exit

import qualified Lexer as L
import qualified Parser as P
import qualified Source as S
import qualified CPS as K
import qualified CC as C
import qualified Hoist as H
import qualified Emit as E

-- src :: S.Term
-- src = S.TmApp (S.TmLam x (S.TmFst (S.TmVarOcc x))) (S.TmPair (S.TmInt 17) (S.TmInt 32))
--   where x = S.TmVar "x"

-- TODO: A native string type, probably like 'Text' not [Char]?

-- TODO: case inr 33 of inl x -> x + 1; inr y -> y - 3
-- src :: S.Term
-- src = S.TmCase (S.TmInr (S.TmInt 33)) x (S.TmAdd (S.TmVarOcc x) (S.TmInt 1)) y (S.TmAdd (S.TmVarOcc y) (S.TmInt (-3)))
--   where
--     x = S.TmVar "x"
--     y = S.TmVar "y"

-- TODO: Implement ==
-- TODO: Test factorial.

-- Note: Returning multiple values from a function is passing multiple values
-- to the continuation.

parseString :: String -> IO S.Term
parseString s = case P.parseTerm (L.lex s) of
  Left P.EOF -> putStrLn "unexpected EOF" >> exitFailure
  Left (P.ErrorAt msg) -> putStrLn ("parse error:" ++ msg) >> exitFailure
  Right x -> pure x

parseFile :: FilePath -> IO S.Term
parseFile f = readFile f >>= parseString

src :: String
-- src = "let fun f x = case iszero x of { inl z -> 33; inr z -> f (x + -1) }; in f 10"
src = "let fun f x = case iszero x of { inl z -> 0; inr z -> x + f (x + -1) }; in f 10"

main :: IO ()
main = do
  srcS <- parseString src

  putStrLn $ "--- CPS Transform ---"
  let srcK = K.cpsMain srcS
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
