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
import qualified CPS.TypeCheck as KT
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
  , driverOutFile :: Maybe String
  , driverDumpCPS :: Bool
  , driverDumpCC :: Bool
  , driverDumpHoist :: Bool
  , driverDumpEmit :: Bool
  , driverNoExe :: Bool
  , driverCheckCPS :: Bool
  , driverASAN :: Bool
  }

driver :: Parser DriverArgs
driver = DriverArgs
  <$> argument str (metavar "FILE")
  <*> optional (strOption (short 'o' <> metavar "FILENAME" <> help "Output location"))
  <*> switch (long "dump-cps" <> help "whether to dump CPS IR")
  <*> switch (long "dump-cc" <> help "whether to dump CC IR")
  <*> switch (long "dump-hoist" <> help "whether to dump Hoist IR")
  <*> switch (long "dump-emit" <> help "whether to dump Emit C output")
  <*> switch (long "no-exe" <> help "do not invoke clang on the generated C output")
  <*> switch (long "check-cps" <> help "whether to run the typechecker on CPS IR")
  <*> switch (long "with-asan" <> help "compile binaries with AddressSanitizer (developer tool)")

opts :: ParserInfo DriverArgs
opts = info (helper <*> driver) (fullDesc <> progDesc "Compile LambdaC")

main :: IO ()
main = do
  args <- execParser opts

  srcS <- parseFile (driverFile args)
  case T.checkProgram srcS of
    Left err -> do
      putStrLn "type error:"
      putStrLn $ show err
      exitFailure
    Right () -> pure ()

  let (srcK, _ty) = K.cpsMain srcS
  when (driverCheckCPS args) $ do
    case KT.checkProgram srcK of
      Left err -> do
        putStrLn "CPS: typecheck error:"
        putStrLn $ show err
        exitFailure
      Right () -> do
        putStrLn "CPS: typecheck OK"
  when (driverDumpCPS args) $ do
    putStrLn $ "--- CPS Transform ---"
    putStrLn $ K.pprintTerm 0 srcK

  let srcC = C.runConv $ C.cconv srcK
  when (driverDumpCC args) $ do
    putStrLn $ "--- Closure Conversion ---"
    putStrLn $ C.pprintTerm 0 srcC

  let (srcH, (H.ClosureDecls closureDecls, thunkDecls2)) = H.runHoist $ H.hoist srcC
  when (driverDumpHoist args) $ do
    putStrLn $ "--- Hoisting ---"
    putStrLn $ H.pprintThunkTypes thunkDecls2 ++ H.pprintClosures closureDecls ++ H.pprintTerm 0 srcH

  let obj = unlines $ E.emitProgram (thunkDecls2, closureDecls, srcH)
  when (driverDumpEmit args) $ do
    putStrLn $ "--- Code Generation ---"
    putStrLn obj

  let
    (outputFile, executableFile) = case driverOutFile args of
      Nothing -> ( takeFileName (driverFile args) -<.> ".out.c"
                 , dropExtension (takeFileName (driverFile args))
                 )
      Just f -> (f <.> ".out.c", f)
  writeFile outputFile obj

  when (not $ driverNoExe args) $ do
    let clangArgs = ["-I./rts/", "-L./rts/", "-lrts", outputFile, "-o", executableFile]
    let clangArgs' = if driverASAN args then "-g" : "-fsanitize=address" : clangArgs else clangArgs
    let compileProcess = proc "clang" clangArgs'
    exitCode <- runProcess compileProcess
    case exitCode of
      ExitSuccess -> pure ()
      ExitFailure i -> putStrLn ("error: Compilation failed with exit code " ++ show i) >> exitFailure
