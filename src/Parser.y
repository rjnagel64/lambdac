
{
module Parser where

import Data.List (intercalate)

import Lexer
import Loc (loc)

import qualified Data.DList as DL
import Data.DList (DList)

import Source
}

%name parseTerm Term
%name parseProgram Program

%tokentype { Token }
%monad { Either ParseError }
%error { parseError }

%token
  '\\' { TokLambda _ }
  '->' { TokArrow _ }
  '<-' { TokBind _ }
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
  '%' { TokPercent _ }
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
  'data' { TokData _ }
  'pure' { TokPure _ }
  'getLine' { TokGetLine _ }
  'putLine' { TokPutLine _ }
  'runIO' { TokRunIO _ }

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

Program :: { Program }
	: DataDecls Term { Program (DL.toList $1) $2 }
	| Term { Program [] $1 }

DataDecls :: { DList DataDecl }
	  : DataDecl { DL.singleton $1 }
	  | DataDecls DataDecl { DL.snoc $1 $2 }

DataDecl :: { DataDecl }
	 : 'data' ID '=' '{' CtorDecls '}' { DataDecl (tcon $2) [] (DL.toList $5) }
	 | 'data' ID TyBinds '=' '{' CtorDecls '}' { DataDecl (tcon $2) (DL.toList $3) (DL.toList $6) }

TyBinds :: { DList (TyVar, Kind) }
	: TyBind { DL.singleton $1 }
	| TyBinds TyBind { DL.snoc $1 $2 }

CtorDecls :: { DList CtorDecl }
	  : CtorDecl { DL.singleton $1 }
	  | CtorDecls ';' CtorDecl { DL.snoc $1 $3 }

CtorDecl :: { CtorDecl }
	 : ID '(' CtorArgs ')' { CtorDecl (ctor $1) (DL.toList $3) }
	 | ID '(' ')' { CtorDecl (ctor $1) [] }

CtorArgs :: { DList Type }
	 : Type { DL.singleton $1 }
	 | CtorArgs ',' Type { DL.snoc $1 $3 }


Term :: { Term }
     : AppTerm { $1 }
     | '\\' '(' ID ':' Type ')' '->' Term { TmLam (var $3) $5 $8 }
     | '\\' '@' ID '->' Term { TmTLam (tvar $3) KiStar $5 }
     | 'let' ID ':' Type '=' Term 'in' Term { TmLet (var $2) $4 $6 $8 }
     | 'let' ID ':' Type '<-' Term 'in' Term { TmBind (var $2) $4 $6 $8 }
     | 'let' FunBinds 'in' Term { TmRecFun (DL.toList $2) $4 }
     | 'letrec' RecBinds 'in' Term { TmLetRec (DL.toList $2) $4 }
     | 'case' Term 'return' Type 'of' '{' 'inl' '(' ID ':' Type ')' '->' Term ';' 'inr' '(' ID ':' Type ')' '->' Term '}'
       { TmCaseSum $2 $4 (var $9, $11, $14) (var $18, $20, $23) }
     | 'if' Term 'return' Type 'then' Term 'else' Term { TmIf $2 $4 $6 $8 }
     | 'case' Term 'return' Type 'of' '{' Alts '}' { TmCase $2 $4 (DL.toList $7) }

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
     | 'fst' ATerm { TmFst $2 }
     | 'snd' ATerm { TmSnd $2 }
     | 'pure' ATerm { TmPure $2 }
     | 'putLine' ATerm { TmPutLine $2 }
     | 'runIO' ATerm { TmRunIO $2 }
     | '-' ATerm %prec UMINUS { TmNegate $2 }

Alts :: { DList (Ctor, [(TmVar, Type)], Term) }
     : {- empty -} { DL.empty }
     | Alt { DL.singleton $1 }
     | Alts ';' Alt { DL.snoc $1 $3 }

Alt :: { (Ctor, [(TmVar, Type)], Term) }
    -- Shift-reduce conflict
    -- ID '(' | ... '->' ... should always shift, but for some reason the LR
    -- automaton considered the possibility of reducing a list of zero varbinds
    -- and then trying to parse '(' as the RHS.
    --
    -- Therefore, the rule is manually split to avoid such nonsense.
    : ID '->' Term { (ctor $1, [], $3) }
    | ID VarBinds '->' Term { (ctor $1, DL.toList $2, $4) }

VarBinds :: { DList (TmVar, Type) }
	 : VarBind { DL.singleton $1 }
	 | VarBinds VarBind { DL.snoc $1 $2 }

AppTerm :: { Term }
        : ATerm { $1 }
        | AppTerm ATerm { TmApp $1 $2 }
        | AppTerm '@' AType { TmTApp $1 $3 }

ATerm :: { Term }
     : '(' Term ')' { $2 }
     | '(' ')' { TmNil }
     | '(' Term ',' Term ')' { TmPair $2 $4 }
     | ID { TmVarOcc (var $1) }
     | '%' ID { TmCtorOcc (ctor $2) }
     | INT { TmInt (int $1) }
     | STRING { TmString (string $1) }
     | 'true' { TmBool True }
     | 'false' { TmBool False }
     | 'getLine' { TmGetLine }

VarBind :: { (TmVar, Type) }
        : '(' ID ':' Type ')' { (var $2, $4) }

FunBinds :: { DList TmFun }
         : FunBind { DL.singleton $1 }
         | FunBinds FunBind { DL.snoc $1 $2 }

FunBind :: { TmFun }
        : 'fun' ID '(' ID ':' Type ')' ':' Type '=' Term ';' { TmFun (var $2) (var $4) $6 $9 $11 }

RecBinds :: { DList (TmVar, Type, Term) }
         : RecBind { DL.singleton $1 }
         | RecBinds RecBind { DL.snoc $1 $2 }

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
	| AppType AType { TyApp $1 $2 }

AType :: { Type }
      : '(' Type ')' { $2 }
      | 'unit' { TyUnit }
      | 'int' { TyInt }
      | 'bool' { TyBool }
      | 'string' { TyString }
      -- As in terms, I need to distinguish (type) variable occurrences from
      -- (type) constructors.
      -- For now, I prefix (type) constructors with a sigil.
      -- Alternately, I could include a name resolution pass, or make type
      -- variables 'a 'b 'c as in ML.
      | ID { TyVarOcc (tvar $1) }
      | '%' ID { TyConOcc (tcon $2) }

Kind :: { Kind }
     : '*' { KiStar }

TyBind :: { (TyVar, Kind) }
       : '(' ID ':' Kind ')' { (tvar $2, $4) }

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

tcon :: Token -> TyCon
tcon (TokID _ s) = TyCon s

ctor :: Token -> Ctor
ctor (TokID _ s) = Ctor s

int :: Token -> Int
int (TokINT _ s) = read s

string :: Token -> String
string (TokSTRING _ s) = read s -- remove initial/final quote and process escapes.
}
