
{
module Parser where

import Data.List (intercalate)

import Lexer
import Loc

import Source
}

%name parseTerm Term

%tokentype { Token }
%monad { Either ParseError }
%error { parseError }

%token
  '\\' { TokLambda _ }
  '->' { TokArrow _ }
  '=' { TokEquals _ }
  '*' { TokStar _ }
  '+' { TokPlus _ }
  ';' { TokSemi _ }
  ':' { TokColon _ }
  '.' { TokDot _ }
  '(' { TokLParen _ }
  ')' { TokRParen _ }
  '{' { TokLBrace _ }
  '}' { TokRBrace _ }
  'fun' { TokFun _ }
  'case' { TokCase _ }
  'of' { TokOf _ }
  'inl' { TokInl _ }
  'inr' { TokInr _ }
  'fst' { TokFst _ }
  'snd' { TokSnd _ }
  'true' { TokTrue _ }
  'false' { TokFalse _ }
  'if' { TokIf _ }
  'then' { TokThen _ }
  'else' { TokElse _ }

  ID { TokID _ _ }
  INT { TokINT _ _ }

-- Precedence goes here, low to high

%right '->'
%left '+'

%%

Term :: { Term }
     : AppTerm { $1 }
     -- precedence: `λx -> e1 + e2` should be `λx -> (e1 + e2)`, not `(λx -> e1) + e2`.
     | '\\' ID '->' Term { TmLam (var $2) $4 }
     | Term '+' Term { TmAdd $1 $3 }
     | 'case' Term 'of' '{' 'inl' ID '->' Term ';' 'inr' ID '->' Term '}'
       { TmCase $2 (var $6) $8 (var $11) $13 }
     | 'inl' ATerm { TmInl $2 }
     | 'inr' ATerm { TmInr $2 }
     | 'fst' ATerm { TmFst $2 }
     | 'snd' ATerm { TmSnd $2 }

AppTerm :: { Term }
        : ATerm { $1 }
        | AppTerm ATerm { TmApp $1 $2 }

ATerm :: { Term }
     : '(' Term ')' { $2 }
     | '(' ')' { TmNil }
     | ID { TmVarOcc (var $1) }
     | INT { TmInt (int $1) }

{
data ParseError = EOF | ErrorAt String

instance Show ParseError where
  show EOF = "unexpected EOF"
  show (ErrorAt s) = s

parseError :: [Token] -> Either ParseError a
parseError ts = Left EOF
parseError ts@(token:_) = Left $
  ErrorAt $ show (loc token) <> ": Parse Error:\n  " <> (intercalate "\n  " (show <$> take 5 ts))

var :: Token -> TmVar
var (TokID _ s) = TmVar s

int :: Token -> Int
int (TokINT _ s) = read s
}
