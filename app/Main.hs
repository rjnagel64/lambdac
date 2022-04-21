{-# LANGUAGE DataKinds #-}

module Main where

import Control.Monad (when)
import System.Exit
import Options.Applicative
import System.Process.Typed
import System.FilePath

import qualified Lexer as L
import qualified Parser as P
import qualified Source as S
import qualified TypeCheck as T
import qualified CPS as K
import qualified CC as C
import qualified Hoist as H
import qualified Emit as E

-- Note: Returning multiple values from a function is passing multiple values
-- to the continuation.
-- Note: Returning a choice of values from a function is selecting which
-- continuation to invoke.
--
-- Note: Performing arity analyses on CPS code is more challenging/obfuscated
-- than I previously comprehended. It may be worthwhile to do that sort of
-- analysis on Source instead.

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

-- TODO: Support -o driver flag
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
  srcK <- case K.cpsMain srcS of
    Left err -> do
      putStrLn "type error:"
      putStrLn $ show err
      exitFailure
    Right (srcK, _t) -> pure srcK
  when (driverDumpCPS args) $ do
    putStrLn $ "--- CPS Transform ---"
    putStrLn $ K.pprintTerm 0 srcK

  let (srcC, thunkDecls) = C.runConv $ C.cconv srcK
  when (driverDumpCC args) $ do
    putStrLn $ "--- Closure Conversion ---"
    putStrLn $ concatMap C.pprintThunkType thunkDecls ++ C.pprintTerm 0 srcC

  let (srcH, H.ClosureDecls closureDecls) = H.runHoist $ H.hoist srcC
  when (driverDumpHoist args) $ do
    putStrLn $ "--- Hoisting ---"
    putStrLn $ H.pprintClosures closureDecls ++ H.pprintTerm 0 srcH

  let obj = unlines $ E.emitProgram (thunkDecls, closureDecls, srcH)
  when (driverDumpEmit args) $ do
    putStrLn $ "--- Code Generation ---"
    putStrLn obj

  -- TODO: Use temporary file for C output by default?
  let outputFile = takeFileName (driverFile args) -<.> ".out.c"
  let executableFile = dropExtension (takeFileName (driverFile args))
  writeFile outputFile obj

  -- TODO: Flag to skip invoking clang, merely output the C code
  -- (e.g., to debug code-gen errors/warnings)
  -- --no-executable, maybe?
  let compileProcess = proc "clang" ["-I./rts/", "-L./rts/", "-lrts", outputFile, "-o", executableFile]
  exitCode <- runProcess compileProcess
  case exitCode of
    ExitSuccess -> pure ()
    ExitFailure i -> putStrLn ("error: Compilation failed with exit code " ++ show i) >> exitFailure
