
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
  '-' { TokMinus _ }
  ';' { TokSemi _ }
  ':' { TokColon _ }
  '.' { TokDot _ }
  ',' { TokComma _ }
  '(' { TokLParen _ }
  ')' { TokRParen _ }
  '{' { TokLBrace _ }
  '}' { TokRBrace _ }
  '<' { TokLAngle _ }
  '>' { TokRAngle _ }
  'fun' { TokFun _ }
  'case' { TokCase _ }
  'of' { TokOf _ }
  'let' { TokLet _ }
  'in' { TokIn _ }
  'inl' { TokInl _ }
  'inr' { TokInr _ }
  'fst' { TokFst _ }
  'snd' { TokSnd _ }
  'iszero' { TokIsZero _ } -- TODO: Replace with `\x -> x == 0`
  'true' { TokTrue _ }
  'false' { TokFalse _ }
  'if' { TokIf _ }
  'then' { TokThen _ }
  'else' { TokElse _ }
  'unit' { TokUnit _ }
  'forall' { TokForall _ }

  ID { TokID _ _ }
  INT { TokINT _ _ }

-- Precedence goes here, low to high

%right '->' 'in'
%left '+' '-'
%left '*'

%%

Term :: { Term }
     : AppTerm { $1 }
     | '\\' ID '->' Term { TmLam (var $2) $4 }
     | 'let' ID '=' Term 'in' Term { TmLet (var $2) $4 $6 }
     | 'let' FunBinds 'in' Term { TmRecFun $2 $4 }
     | 'case' Term 'of' '{' 'inl' ID '->' Term ';' 'inr' ID '->' Term '}'
       { TmCase $2 (var $6) $8 (var $11) $13 }

     | Term '+' Term { TmAdd $1 $3 }
     | Term '-' Term { TmSub $1 $3 }
     | Term '*' Term { TmMul $1 $3 }

     | 'inl' ATerm { TmInl $2 }
     | 'inr' ATerm { TmInr $2 }
     | 'fst' ATerm { TmFst $2 }
     | 'snd' ATerm { TmSnd $2 }
     | 'iszero' ATerm { TmIsZero $2 }

AppTerm :: { Term }
        : ATerm { $1 }
        | AppTerm ATerm { TmApp $1 $2 }

ATerm :: { Term }
     : '(' Term ')' { $2 }
     | '(' ')' { TmNil }
     | '(' Term ',' Term ')' { TmPair $2 $4 }
     | ID { TmVarOcc (var $1) }
     | INT { TmInt (int $1) }

FunBinds :: { [TmFun] }
         : FunBind { [$1] }
         | FunBinds FunBind { $1 ++ [$2] } -- TODO: DList

FunBind :: { TmFun }
        : 'fun' ID ID '=' Term ';' { TmFun (var $2) (var $3) $5 }

Type :: { Type }
     : AType { $1 }
     | AType '->' Type { TyArr $1 $3 }
     | 'forall' ID '.' Type { TyAll (tvar $2) $4 }

AType :: { Type }
      : '(' Type ')' { $2 }
      | 'unit' { TyUnit }
      | ID { TyVarOcc (tvar $1) }

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

tvar :: Token -> TyVar
tvar (TokID _ s) = TyVar s

int :: Token -> Int
int (TokINT _ s) = read s
}
