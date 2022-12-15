
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
  '==' { TokDEquals _ }
  '!=' { TokNEquals _ }
  '=' { TokEquals _ }
  '<=' { TokLe _ }
  '<' { TokLAngle _ }
  '>=' { TokGe _ }
  '>' { TokRAngle _ }
  '@' { TokAt _ }
  '*' { TokStar _ }
  '+' { TokPlus _ }
  '-' { TokMinus _ }
  '^' { TokCaret _ }
  ';' { TokSemi _ }
  ':' { TokColon _ }
  '.' { TokDot _ }
  ',' { TokComma _ }
  '(' { TokLParen _ }
  ')' { TokRParen _ }
  '{' { TokLBrace _ }
  '}' { TokRBrace _ }
  'fun' { TokFun _ }
  'case' { TokCase _ }
  'of' { TokOf _ }
  'return' { TokReturn _ }
  'let' { TokLet _ }
  'letrec' { TokLetRec _ }
  'in' { TokIn _ }
  'inl' { TokInl _ }
  'inr' { TokInr _ }
  'fst' { TokFst _ }
  'snd' { TokSnd _ }
  'true' { TokTrue _ }
  'false' { TokFalse _ }
  'if' { TokIf _ }
  'then' { TokThen _ }
  'else' { TokElse _ }
  'unit' { TokUnit _ }
  'int' { TokInt _ }
  'bool' { TokBool _ }
  'string' { TokString _ }
  'forall' { TokForall _ }
  'nil' { TokNil _ }
  'cons' { TokCons _ }
  'list' { TokList _ }
  'uncons' { TokUncons _ }

  ID { TokID _ _ }
  INT { TokINT _ _ }
  STRING { TokSTRING _ _ }

-- Precedence goes here, low to high
-- Actually, I beginning to wish that I could have different precedence
-- specifications for (e.g.) Type and Term.
-- Unfortunately, that does not seem to be possible.

%right '.'
%right '->' 'in' 'else'
%nonassoc '==' '!=' '<' '<=' '>' '>='
%left '^'
%left '+' '-'
%left '*'
%right UMINUS

%%

Term :: { Term }
     : AppTerm { $1 }
     | '\\' '(' ID ':' Type ')' '->' Term { TmLam (var $3) $5 $8 }
     | '\\' '@' ID '->' Term { TmTLam (tvar $3) KiStar $5 }
     | 'let' ID ':' Type '=' Term 'in' Term { TmLet (var $2) $4 $6 $8 }
     | 'let' FunBinds 'in' Term { TmRecFun (rundl $2) $4 }
     | 'letrec' RecBinds 'in' Term { TmLetRec (rundl $2) $4 }
     | 'case' Term 'return' Type 'of' '{' 'inl' '(' ID ':' Type ')' '->' Term ';' 'inr' '(' ID ':' Type ')' '->' Term '}'
       { TmCase $2 $4 (var $9, $11, $14) (var $18, $20, $23) }
     | 'case' 'uncons' Term 'return' Type 'of' '{' 'nil' '->' Term ';' 'cons' VarBind VarBind '->' Term '}'
       { TmCaseList $3 $5 $10 ($13, $14, $16) }
     | 'if' Term 'return' Type 'then' Term 'else' Term { TmIf $2 $4 $6 $8 }

     | Term '+' Term { TmArith $1 TmArithAdd $3 }
     | Term '-' Term { TmArith $1 TmArithSub $3 }
     | Term '*' Term { TmArith $1 TmArithMul $3 }
     | Term '==' Term { TmCmp $1 TmCmpEq $3 }
     | Term '!=' Term { TmCmp $1 TmCmpNe $3 }
     | Term '<' Term { TmCmp $1 TmCmpLt $3 }
     | Term '<=' Term { TmCmp $1 TmCmpLe $3 }
     | Term '>' Term { TmCmp $1 TmCmpGt $3 }
     | Term '>=' Term { TmCmp $1 TmCmpGe $3 }
     | Term '^' Term { TmConcat $1 $3 }

     | 'inl' '@' AType '@' AType ATerm { TmInl $3 $5 $6 }
     | 'inr' '@' AType '@' AType ATerm { TmInr $3 $5 $6 }
     | 'nil' '@' AType { TmEmpty $3 }
     | 'cons' ATerm ATerm { TmCons $2 $3 }
     | 'fst' ATerm { TmFst $2 }
     | 'snd' ATerm { TmSnd $2 }
     | '-' ATerm %prec UMINUS { TmNegate $2 }

AppTerm :: { Term }
        : ATerm { $1 }
        | AppTerm ATerm { TmApp $1 $2 }
        | AppTerm '@' AType { TmTApp $1 $3 }

ATerm :: { Term }
     : '(' Term ')' { $2 }
     | '(' ')' { TmNil }
     | '(' Term ',' Term ')' { TmPair $2 $4 }
     | ID { TmVarOcc (var $1) }
     | INT { TmInt (int $1) }
     | STRING { TmString (string $1) }
     | 'true' { TmBool True }
     | 'false' { TmBool False }

VarBind :: { (TmVar, Type) }
        : '(' ID ':' Type ')' { (var $2, $4) }

FunBinds :: { DList TmFun }
         : FunBind { dlsingle $1 }
         | FunBinds FunBind { snoc $2 $1 }

FunBind :: { TmFun }
        : 'fun' ID '(' ID ':' Type ')' ':' Type '=' Term ';' { TmFun (var $2) (var $4) $6 $9 $11 }

RecBinds :: { DList (TmVar, Type, Term) }
         : RecBind { dlsingle $1 }
         | RecBinds RecBind { snoc $2 $1 }

RecBind :: { (TmVar, Type, Term) }
        : ID ':' Type '=' Term ';' { (var $1, $3, $5) }

Type :: { Type }
     : AppType { $1 }
     | Type '->' Type { TyArr $1 $3 }
     -- Note: product types are left-associative, because '*' is declared %left.
     -- I'm not quite sure I like that. In particular, ((x, y), z) : a * b * c
     -- but I would prefer ((x, y), z): (a * b) * c
     | Type '*' Type { TyProd $1 $3 }
     | Type '+' Type { TySum $1 $3 }
     | 'forall' ID '.' Type { TyAll (tvar $2) KiStar $4 }

AppType :: { Type }
        : AType { $1 }
        | 'list' AppType { TyList $2 }

AType :: { Type }
      : '(' Type ')' { $2 }
      | 'unit' { TyUnit }
      | 'int' { TyInt }
      | 'bool' { TyBool }
      | 'string' { TyString }
      | ID { TyVarOcc (tvar $1) }

{
data ParseError = EOF | ErrorAt String

instance Show ParseError where
  show EOF = "unexpected EOF"
  show (ErrorAt s) = s

parseError :: [Token] -> Either ParseError a
parseError [] = Left EOF
parseError ts@(token:_) = Left $
  ErrorAt $ show (loc token) <> ": Parse Error:\n  " <> (intercalate "\n  " (show <$> take 5 ts))

var :: Token -> TmVar
var (TokID _ s) = TmVar s

tvar :: Token -> TyVar
tvar (TokID _ s) = TyVar s

int :: Token -> Int
int (TokINT _ s) = read s

string :: Token -> String
string (TokSTRING _ s) = read s -- remove initial/final quote and process escapes.
}
