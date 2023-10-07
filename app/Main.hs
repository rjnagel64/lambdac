{-# LANGUAGE DataKinds #-}

module Main where

import Control.Monad (when)
import Data.Foldable (traverse_, foldl')
import System.Exit
import Options.Applicative
import System.Process.Typed
import System.FilePath

import qualified Lexer as Lx
import qualified Parser as P
import qualified Resolve as R
import qualified Core.TypeCheck as ST
import qualified CPS as K
import qualified CPS.IR as K -- for K.Program, for applyOpts :: [OptPass] -> K.Program -> K.Program
import qualified CPS.TypeCheck as KT
import qualified CPS.Uncurry as KU
import qualified CPS.UnusedParams as KU
import qualified CC as C
import qualified CC.TypeCheck as CT
import qualified Hoist as H
import qualified Hoist.TypeCheck as HT
import qualified Backend.Lower as L
import qualified Backend.Emit as E

-- Note: Returning multiple values from a function is passing multiple values
-- to the continuation.
-- Note: Returning a choice of values from a function is selecting which
-- continuation to invoke.
--
-- Note: Performing arity analyses on CPS code is more challenging/obfuscated
-- than I previously comprehended. It may be worthwhile to do that sort of
-- analysis on Source instead.

parseFile :: FilePath -> IO R.Program
parseFile fpath = do
  s <- readFile fpath
  case Lx.lex fpath s of
    Left msg -> putStrLn ("lexical error: " ++ msg) >> exitFailure
    Right toks -> case P.parseProgram toks of
      Left P.EOF -> putStrLn "unexpected EOF" >> exitFailure
      Left (P.ErrorAt l msg) ->
        putStrLn ("parse error: " ++ Lx.displayLoc l ++ ": " ++ msg) >> exitFailure
      Right prog -> pure prog

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
  , driverCheckCC :: Bool
  , driverCheckHoist :: Bool
  , driverASAN :: Bool
  , driverOptPasses :: [OptPass]
  , driverDumpOpt :: Bool
  }

data OptPass = OptUncurry | OptUnusedParams

applyOpt :: OptPass -> K.Program -> K.Program
applyOpt OptUncurry = KU.uncurryProgram
applyOpt OptUnusedParams = KU.dropUnusedParams

applyOpts :: [OptPass] -> K.Program -> K.Program
applyOpts passes program = foldl' (\prog opt -> applyOpt opt prog) program passes

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
  <*> switch (long "check-cc" <> help "whether to run the typechecker on CC IR")
  <*> switch (long "check-hoist" <> help "whether to run the typechecker on Hoist IR")
  <*> switch (long "with-asan" <> help "compile binaries with AddressSanitizer (developer tool)")
  <*> many (option (maybeReader parseOptPass) (long "opt-pass" <> help "apply a CPS optimizaiton pass" <> metavar "PASS"))
  <*> switch (long "dump-opt" <> help "whether to dump optimized CPS IR")

parseOptPass :: String -> Maybe OptPass
parseOptPass "uncurry" = Just OptUncurry
parseOptPass "unused-params" = Just OptUnusedParams
parseOptPass _ = Nothing

opts :: ParserInfo DriverArgs
opts = info (helper <*> driver) (fullDesc <> progDesc "Compile LambdaC")

main :: IO ()
main = do
  args <- execParser opts

  srcR <- parseFile (driverFile args)
  srcS <- case R.resolveProgram srcR of
    Left errs -> do
      putStrLn "name resolution error(s):"
      traverse_ (putStrLn . (" * "++) . R.pprintError) errs
      exitFailure
    Right srcS -> pure srcS
  case ST.checkProgram srcS of
    Left err -> do
      putStrLn "type error:"
      putStrLn $ show err
      exitFailure
    Right () -> pure ()

  let srcK = K.cpsProgram srcS
  when (driverDumpCPS args) $ do
    putStrLn $ "--- CPS Transform ---"
    putStrLn $ K.pprintProgram srcK
  when (driverCheckCPS args) $ do
    case KT.checkProgram srcK of
      Left err -> do
        putStrLn "CPS: typecheck error:"
        putStrLn $ show err
        exitFailure
      Right () -> do
        putStrLn "CPS: typecheck OK"

  let optSrcK = applyOpts (driverOptPasses args) srcK
  when (driverDumpOpt args) $ do
    putStrLn $ "--- Optimized CPS ---"
    putStrLn $ K.pprintProgram optSrcK

  let srcC = C.cconvProgram optSrcK
  when (driverDumpCC args) $ do
    putStrLn $ "--- Closure Conversion ---"
    putStrLn $ C.pprintProgram srcC
  when (driverCheckCC args) $ do
    case CT.checkProgram srcC of
      Left err -> do
        putStrLn "CC: typecheck error:"
        putStrLn $ show err
        exitFailure
      Right () -> do
        putStrLn "CC: typecheck OK"

  let srcH = H.hoistProgram srcC
  when (driverDumpHoist args) $ do
    putStrLn $ "--- Hoisting ---"
    putStrLn $ H.pprintProgram srcH
  when (driverCheckHoist args) $ do
    case HT.checkProgram srcH of
      Left err -> do
        putStrLn "Hoist: typecheck error:"
        putStrLn $ show err
        exitFailure
      Right () -> do
        putStrLn "Hoist: typecheck OK"

  let srcL = L.lowerProgram srcH

  let obj = E.emitProgram srcL
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
    let optArgs = if driverASAN args then ["-g", "-fsanitize=address"] else ["-O2"]
    let compileProcess = proc "clang" (optArgs ++ clangArgs)
    exitCode <- runProcess compileProcess
    case exitCode of
      ExitSuccess -> pure ()
      ExitFailure i -> putStrLn ("error: Compilation failed with exit code " ++ show i) >> exitFailure
