{-# LANGUAGE DataKinds #-}

module Main where

import Experiments.STLC

e :: Term v 'TyBool
e = TmApp (TmLam "x" (\x -> TmVarOcc x)) TmTrue

main :: IO ()
main = do
  putStrLn "Hello, Haskell!"
  putStrLn $ pprintTerm emptyScope $ cpsTerm e
