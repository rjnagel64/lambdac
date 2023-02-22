
{
module Lexer2 (Token(..), L(..), lex) where

import Data.Loc

import Prelude hiding (lex)
}

%wrapper "monadUserState"

$idstart = [a-z A-Z _]
$idcont = [a-z A-Z _ 0-9]
$digit = [0-9]

tokens :-
  -- Comments and whitespace are ignored
  $white+ { skip }
  "--" .* { skip }

  -- Keywords (must occur before identifiers)
  "bool" { simpleToken TokBool }
  "case" { simpleToken TokCase }
  "data" { simpleToken TokData }
  "else" { simpleToken TokElse }
  "false" { simpleToken TokFalse }
  "forall" { simpleToken TokForall }
  "fst" { simpleToken TokFst }
  "fun" { simpleToken TokFun }
  "getLine" { simpleToken TokGetLine }
  "if" { simpleToken TokIf }
  "in" { simpleToken TokIn }
  "inl" { simpleToken TokInl }
  "inr" { simpleToken TokInr }
  "int" { simpleToken TokInt }
  "let" { simpleToken TokLet }
  "letrec" { simpleToken TokLetRec }
  "of" { simpleToken TokOf }
  "pure" { simpleToken TokPure }
  "putLine" { simpleToken TokPutLine }
  "return" { simpleToken TokReturn }
  "runIO" { simpleToken TokRunIO }
  "snd" { simpleToken TokSnd }
  "string" { simpleToken TokString }
  "then" { simpleToken TokThen }
  "true" { simpleToken TokTrue }
  "unit" { simpleToken TokUnit }

  -- Identifiers and literals
  $idstart $idcont* { tokenWithString TokID }
  $digit+ { tokenWithString TokINT }
  \" [^\"]* \" { tokenWithString TokSTRING }

  -- Symbols
  "->" { simpleToken TokArrow }
  "@" { simpleToken TokAt }
  "<-" { simpleToken TokBind }
  "^" { simpleToken TokCaret }
  ":" { simpleToken TokColon }
  "," { simpleToken TokComma }
  "==" { simpleToken TokDEquals }
  "." { simpleToken TokDot }
  "=" { simpleToken TokEquals }
  ">=" { simpleToken TokGe }
  [\\] { simpleToken TokLambda }
  "<" { simpleToken TokLAngle }
  "{" { simpleToken TokLBrace }
  "<=" { simpleToken TokLe }
  "(" { simpleToken TokLParen }
  "-" { simpleToken TokMinus }
  "!=" { simpleToken TokNEquals }
  "%" { simpleToken TokPercent }
  "+" { simpleToken TokPlus }
  "}" { simpleToken TokRBrace }
  ")" { simpleToken TokRParen }
  ">" { simpleToken TokRAngle }
  ";" { simpleToken TokSemi }
  "*" { simpleToken TokStar }

{

-- Section: Public API:

-- | Perform lexical analysis on an input string.
lex :: FilePath -> String -> Either String [L Token]
lex fpath input = runAlex input $ alexSetFilePath fpath >> loop
  where
    loop = do
      tok <- alexMonadScan
      case tok of
        L _ TokEOF -> return []
        _ -> (tok :) <$> loop

-- | Tokens that can be produced by the lexical analyzer.
data Token
  -- Hmm. EOF needed by 'alexEOF :: Alex (L Token)', but is not included in the token stream.
  = TokEOF
  -- Literals and identifiers
  | TokID String
  | TokINT String
  | TokSTRING String
  -- Symbols (order: alphabetical by name)
  | TokArrow
  | TokAt
  | TokBind
  | TokCaret
  | TokColon
  | TokComma
  | TokDEquals
  | TokDot
  | TokEquals
  | TokGe
  | TokLambda
  | TokLAngle
  | TokLBrace
  | TokLe
  | TokLParen
  | TokMinus
  | TokNEquals
  | TokPercent
  | TokPlus
  | TokRBrace
  | TokRParen
  | TokRAngle
  | TokSemi
  | TokStar
  -- Keywords (order: alphabetical by name)
  | TokBool
  | TokCase
  | TokData
  | TokElse
  | TokFalse
  | TokForall
  | TokFst
  | TokFun
  | TokGetLine
  | TokIf
  | TokIn
  | TokInl
  | TokInr
  | TokInt
  | TokLet
  | TokLetRec
  | TokOf
  | TokPure
  | TokPutLine
  | TokReturn
  | TokRunIO
  | TokSnd
  | TokString
  | TokThen
  | TokTrue
  | TokUnit
  deriving Show


-- Section: Things required by the monadUserState wrapper:

-- | Extra state we inject into the Alex monad.
-- Specifically, we keep track of the file path of the file currently being
-- analyzed, to compute source locations with file info.
type AlexUserState = FilePath

-- | The initial user state used by Alex.
alexInitUserState :: AlexUserState
alexInitUserState = "<no file>"

-- | An action to set the user state to the path of the file being lexed.
alexSetFilePath :: FilePath -> Alex ()
alexSetFilePath fpath = Alex $ \s -> Right (s { alex_ust = fpath }, ())

alexEOF :: Alex (L Token)
alexEOF = return (L NoLoc TokEOF)


-- Section: Helper functions for lexer actions:

-- | Turn Alex's position+length into a proper source location.
makeLoc :: AlexPosn -> Int -> Alex Loc
makeLoc (AlexPn off line col) len = do
  fpath <- alexGetUserState
  let startpos = Pos fpath line col off
  let endpos = Pos fpath line (col + len) (off + len)
  return (Loc startpos endpos)

-- | A helper function for constructing a token.
simpleToken :: Token -> AlexAction (L Token)
simpleToken t (pos, _prev, _bytes, _input) len = do
  l <- makeLoc pos len
  return (L l t)

-- | A helper function for constructing a token from the matched text.
tokenWithString :: (String -> Token) -> AlexAction (L Token)
tokenWithString f (pos, _prev, _bytes, input) len = do
  l <- makeLoc pos len
  let content = take len input
  return (L l (f content))

}

-- vim: set et sts=2 sw=2:
