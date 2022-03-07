{-# LANGUAGE DataKinds #-}

module Main where

import Control.Monad (when)
import System.Exit
import Options.Applicative

import qualified Lexer as L
import qualified Parser as P
import qualified Source as S
import qualified CPS as K
import qualified CC as C
import qualified Hoist as H
import qualified Emit as E

-- TODO: Implement ==
-- TODO: Test factorial.

-- Note: Returning multiple values from a function is passing multiple values
-- to the continuation.
-- Note: Returning a choice of values from a function is selecting which
-- continuation to invoke.

parseString :: String -> IO S.Term
parseString s = case P.parseTerm (L.lex s) of
  Left P.EOF -> putStrLn "unexpected EOF" >> exitFailure
  Left (P.ErrorAt msg) -> putStrLn ("parse error:" ++ msg) >> exitFailure
  Right x -> pure x

parseFile :: FilePath -> IO S.Term
parseFile f = readFile f >>= parseString

data DriverArgs
  = DriverArgs {
    driverFile :: String
  , driverDumpCPS :: Bool
  , driverDumpCC :: Bool
  , driverDumpHoist :: Bool
  , driverDumpEmit :: Bool
  }

driver :: Parser DriverArgs
driver = DriverArgs
  <$> argument str (metavar "FILE")
  <*> switch (long "dump-cps" <> help "whether to dump CPS IR")
  <*> switch (long "dump-cc" <> help "whether to dump CC IR")
  <*> switch (long "dump-hoist" <> help "whether to dump Hoist IR")
  <*> switch (long "dump-emit" <> help "whether to dump Emit C output")

opts :: ParserInfo DriverArgs
opts = info (helper <*> driver) (fullDesc <> progDesc "Compile LambdaC")

main :: IO ()
main = do
  args <- execParser opts

  srcS <- parseFile (driverFile args)

  let (srcK, _) = K.cpsMain srcS
  when (driverDumpCPS args) $ do
    putStrLn $ "--- CPS Transform ---"
    putStrLn $ K.pprintTerm 0 srcK

  let srcC = C.runConv $ C.cconv srcK
  when (driverDumpCC args) $ do
    putStrLn $ "--- Closure Conversion ---"
    putStrLn $ C.pprintTerm 0 srcC

  let (srcH, decls) = H.runHoist $ H.hoist srcC
  when (driverDumpHoist args) $ do
    putStrLn $ "--- Hoisting ---"
    putStrLn $ H.pprintDecls decls ++ H.pprintTerm 0 srcH

  let obj = unlines $ E.emitProgram (decls, srcH)
  when (driverDumpEmit args) $ do
    putStrLn $ "--- Code Generation ---"
    putStrLn obj

  -- TODO: Name output file based on input file
  -- TODO: Generate Makefile fragment? Yes. Gen-C each module, Gen-makefile, make -f $exe.make $exe
  writeFile "out.c" obj
