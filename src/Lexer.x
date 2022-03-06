
{
module Lexer
    ( Token(..)
    , lex
    ) where

import Prelude hiding (lex)

import Loc
}

%wrapper "posn"


$digit = [0-9]
$lc = [a-z_]
$uc = [A-Z]

$lcidstart = $lc
$lcidcont = [$lc $uc $digit \-]

$ucidstart = $uc
$ucidcont = [$lc $uc $digit \-]

$idstart = [$lc $uc]
$idcont = [$lc $uc $digit \-]

tokens :-
  $white+ ;
  "--" .* ;

  [\\] { tok TokLambda }
  "->" { tok TokArrow }
  ";" { tok TokSemi }
  ":" { tok TokColon }
  "." { tok TokDot }
  "," { tok TokComma }
  "=" { tok TokEquals }
  "*" { tok TokStar }
  "+" { tok TokPlus }
  "-" { tok TokMinus }

  "(" { tok TokLParen }
  ")" { tok TokRParen }
  "{" { tok TokLBrace }
  "}" { tok TokRBrace }
  "<" { tok TokLAngle }
  ">" { tok TokRAngle }

  "fun" { tok TokFun }
  "let" { tok TokLet }
  "in" { tok TokIn }
  "case" { tok TokCase }
  "of" { tok TokOf }
  "inl" { tok TokInl }
  "inr" { tok TokInr }
  "fst" { tok TokFst }
  "snd" { tok TokSnd }
  "iszero" { tok TokIsZero }
  "true" { tok TokTrue }
  "false" { tok TokFalse }
  "if" { tok TokIf }
  "then" { tok TokThen }
  "else" { tok TokElse }
  "unit" { tok TokUnit }
  "forall" { tok TokForall }

  [\- \+]? $digit+ { toks TokINT }

  $idstart $idcont* { toks TokID }

{
-- Other lexer utilities. These can't go in `Loc` because they depend on Alex.
tok :: (Loc -> Token) -> AlexPosn -> String -> Token
tok kont pos s = kont (mkLoc pos s)

toks :: (Loc -> String -> Token) -> AlexPosn -> String -> Token
toks kont pos s = kont (mkLoc pos s) s

mkLoc :: AlexPosn -> String -> Loc
mkLoc (AlexPn absPos lin col) s =
  Loc {
    locOffset = absPos
  , locLine = lin
  , locCol = col
  , locLength = length s
  }

-- | Tokens in an ML-ish language.
data Token
  = TokLambda Loc
  | TokArrow Loc
  | TokSemi Loc
  | TokColon Loc
  | TokDot Loc
  | TokComma Loc
  | TokEquals Loc
  | TokStar Loc
  | TokPlus Loc
  | TokMinus Loc

  | TokLParen Loc
  | TokRParen Loc
  | TokLBrace Loc
  | TokRBrace Loc
  | TokLAngle Loc
  | TokRAngle Loc

  | TokID Loc String
  | TokINT Loc String

  -- Would it be worthwhile to consolidate these into 'TokKW KW Loc';
  -- data KW = Case | Fun | In | ...?
  | TokCase Loc
  | TokOf Loc
  | TokFun Loc
  | TokIn Loc
  | TokLet Loc

  | TokInl Loc
  | TokInr Loc
  | TokFst Loc
  | TokSnd Loc
  | TokIsZero Loc

  | TokTrue Loc
  | TokFalse Loc
  | TokIf Loc
  | TokThen Loc
  | TokElse Loc

  | TokUnit Loc
  | TokForall Loc
  deriving (Show)

instance Located Token where
  loc (TokLambda l) = l
  loc (TokArrow l) = l
  loc (TokSemi l) = l
  loc (TokColon l) = l
  loc (TokDot l) = l
  loc (TokComma l) = l
  loc (TokEquals l) = l
  loc (TokStar l) = l
  loc (TokLParen l) = l
  loc (TokRParen l) = l
  loc (TokLBrace l) = l
  loc (TokRBrace l) = l
  loc (TokLAngle l) = l
  loc (TokRAngle l) = l
  loc (TokPlus l) = l
  loc (TokMinus l) = l
  loc (TokID l _) = l
  loc (TokINT l _) = l
  loc (TokCase l) = l
  loc (TokFun l) = l
  loc (TokIn l) = l
  loc (TokLet l) = l
  loc (TokOf l) = l
  loc (TokInl l) = l
  loc (TokInr l) = l
  loc (TokFst l) = l
  loc (TokSnd l) = l
  loc (TokIsZero l) = l
  loc (TokTrue l) = l
  loc (TokFalse l) = l
  loc (TokIf l) = l
  loc (TokThen l) = l
  loc (TokElse l) = l
  loc (TokUnit l) = l
  loc (TokForall l) = l

-- | Lex a string.
lex :: String -> [Token]
lex = alexScanTokens

}

-- vim: set et sts=2 sw=2:
