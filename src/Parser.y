
{
module Parser where

import Data.List (intercalate)

import Lexer

import qualified Data.DList as DL
import Data.DList (DList)

-- import Source
import Resolve
}

%name parseTerm Term
%name parseProgram Program

%tokentype { L Token }
%monad { Either ParseError }
%error { parseError }

%token
  '\\' { L _ TokLambda }
  '->' { L _ TokArrow }
  '<-' { L _ TokBind }
  '==' { L _ TokDEquals }
  '!=' { L _ TokNEquals }
  '=' { L _ TokEquals }
  '<=' { L _ TokLe }
  '<' { L _ TokLAngle }
  '>=' { L _ TokGe }
  '>' { L _ TokRAngle }
  '@' { L _ TokAt }
  '*' { L _ TokStar }
  '+' { L _ TokPlus }
  '-' { L _ TokMinus }
  '^' { L _ TokCaret }
  ';' { L _ TokSemi }
  ':' { L _ TokColon }
  '.' { L _ TokDot }
  ',' { L _ TokComma }
  '(' { L _ TokLParen }
  ')' { L _ TokRParen }
  '{' { L _ TokLBrace }
  '}' { L _ TokRBrace }
  'bool' { L _ TokBool }
  'case' { L _ TokCase }
  'char' { L _ TokChar }
  'char_at_idx#' { L _ TokCharAtIndex }
  'data' { L _ TokData }
  'else' { L _ TokElse }
  'eq_char#' { L _ TokEqChar }
  'false' { L _ TokFalse }
  'forall' { L _ TokForall }
  'fst' { L _ TokFst }
  'getLine' { L _ TokGetLine }
  'if' { L _ TokIf }
  'in' { L _ TokIn }
  'int' { L _ TokInt }
  'let' { L _ TokLet }
  'letrec' { L _ TokLetRec }
  'of' { L _ TokOf }
  'pure' { L _ TokPure }
  'putLine' { L _ TokPutLine }
  'return' { L _ TokReturn }
  'runIO' { L _ TokRunIO }
  'snd' { L _ TokSnd }
  'string' { L _ TokString }
  'then' { L _ TokThen }
  'true' { L _ TokTrue }
  'unit' { L _ TokUnit }

  ID { L _ (TokID _) }
  INT { L _ (TokINT _) }
  STRING { L _ (TokSTRING _) }
  CHAR { L _ (TokCHAR _) }

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
%left '.'

%%

Program :: { Program }
	: DataDecls Term { Program (DL.toList $1) $2 }
	| Term { Program [] $1 }

DataDecls :: { DList DataDecl }
	  : DataDecl { DL.singleton $1 }
	  | DataDecls DataDecl { DL.snoc $1 $2 }

DataDecl :: { DataDecl }
	 : 'data' ID '=' '{' CtorDecls '}' { DataDecl (ident $2) [] (DL.toList $5) }
	 | 'data' ID TyBinds '=' '{' CtorDecls '}' { DataDecl (ident $2) (DL.toList $3) (DL.toList $6) }

TyBinds :: { DList (ID, Kind) }
	: TyBind { DL.singleton $1 }
	| TyBinds TyBind { DL.snoc $1 $2 }

CtorDecls :: { DList CtorDecl }
	  : CtorDecl { DL.singleton $1 }
	  | CtorDecls ';' CtorDecl { DL.snoc $1 $3 }

CtorDecl :: { CtorDecl }
	 : ID '(' CtorArgs ')' { CtorDecl (ident $1) (DL.toList $3) }
	 | ID '(' ')' { CtorDecl (ident $1) [] }

CtorArgs :: { DList Type }
	 : Type { DL.singleton $1 }
	 | CtorArgs ',' Type { DL.snoc $1 $3 }


-- Okay, the precedence levels here have gotten very messy. I need to go back
-- and clean these up.
-- (In particular, the mix of explicit precedence levels with fixity directives
-- is kind of weird.)
Term :: { Term }
     : AppTerm { $1 }
     | '\\' '(' ID ':' Type ')' '->' Term { TmLam (ident $3) $5 $8 }
     | '\\' '@' ID '->' Term { TmTLam (ident $3) KiStar $5 }
     | 'let' ID ':' Type '=' Term 'in' Term { TmLet (ident $2) $4 $6 $8 }
     | 'let' ID ':' Type '<-' Term 'in' Term { TmBind (ident $2) $4 $6 $8 }
     | 'letrec' RecBinds 'in' Term { TmLetRec (DL.toList $2) $4 }
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
     | Term '^' Term { TmStringOp $1 TmConcat $3 }

     | Term '.' ID { TmFieldProj $1 (fieldLabel $3) }
     | '-' ATerm %prec UMINUS { TmNegate $2 }

     -- These are basically AppTerm:s, aren't they?
     | 'fst' ATerm { TmFst $2 }
     | 'snd' ATerm { TmSnd $2 }
     | 'eq_char#' ATerm ATerm { TmCmp $2 TmCmpEqChar $3 }
     | 'char_at_idx#' ATerm ATerm { TmStringOp $2 TmIndexStr $3 }
     | 'pure' ATerm { TmPure $2 }
     | 'putLine' ATerm { TmPutLine $2 }
     | 'runIO' ATerm { TmRunIO $2 }

AppTerm :: { Term }
        : ATerm { $1 }
        | AppTerm ATerm { TmApp $1 $2 }
        | AppTerm '@' AType { TmTApp $1 $3 }

ATerm :: { Term }
     : '(' Term ')' { $2 }
     | '(' ')' { TmNil }
     | '(' Term ',' Term ')' { TmPair $2 $4 }
     | '{' FieldVals '}' { TmRecord (DL.toList $2) }
     | ID { TmNameOcc (ident $1) }
     | INT { TmInt (int $1) }
     | STRING { TmString (string $1) }
     | CHAR { TmChar (char $1) }
     | 'true' { TmBool True }
     | 'false' { TmBool False }
     | 'getLine' { TmGetLine }

Alts :: { DList (ID, [(ID, Type)], Term) }
     : {- empty -} { DL.empty }
     | Alt { DL.singleton $1 }
     | Alts ';' Alt { DL.snoc $1 $3 }

Alt :: { (ID, [(ID, Type)], Term) }
    -- Shift-reduce conflict
    -- ID '(' | ... '->' ... should always shift, but for some reason the LR
    -- automaton considered the possibility of reducing a list of zero varbinds
    -- and then trying to parse '(' as the RHS.
    --
    -- Therefore, the rule is manually split to avoid such nonsense.
    : ID '->' Term { (ident $1, [], $3) }
    | ID VarBinds '->' Term { (ident $1, DL.toList $2, $4) }

VarBinds :: { DList (ID, Type) }
	 : VarBind { DL.singleton $1 }
	 | VarBinds VarBind { DL.snoc $1 $2 }

FieldVals :: { DList (FieldLabel, Term) }
	  : {- empty -} { DL.empty }
	  | FieldValsNE { $1 }

FieldValsNE :: { DList (FieldLabel, Term) }
	    : FieldVal { DL.singleton $1 }
	    | FieldValsNE ',' FieldVal { DL.snoc $1 $3 }

FieldVal :: { (FieldLabel, Term) }
	 : ID '=' Term { (fieldLabel $1, $3) }

VarBind :: { (ID, Type) }
        : '(' ID ':' Type ')' { (ident $2, $4) }

RecBinds :: { DList (ID, Type, Term) }
         : RecBind { DL.singleton $1 }
         | RecBinds RecBind { DL.snoc $1 $2 }

RecBind :: { (ID, Type, Term) }
        : ID ':' Type '=' Term ';' { (ident $1, $3, $5) }

Type :: { Type }
     : AppType { $1 }
     | Type '->' Type { TyArr $1 $3 }
     -- Note: product types are left-associative, because '*' is declared %left.
     -- I'm not quite sure I like that. In particular, ((x, y), z) : a * b * c
     -- but I would prefer ((x, y), z): (a * b) * c
     | Type '*' Type { TyProd $1 $3 }
     | 'forall' ID '.' Type { TyAll (ident $2) KiStar $4 }

AppType :: { Type }
        : AType { $1 }
	| AppType AType { TyApp $1 $2 }

AType :: { Type }
      : '(' Type ')' { $2 }
      | '{' FieldTys '}' { TyRecord (DL.toList $2) }
      | 'unit' { TyUnit }
      | 'int' { TyInt }
      | 'bool' { TyBool }
      | 'string' { TyString }
      | 'char' { TyChar }
      | ID { TyNameOcc (ident $1) }

FieldTys :: { DList (FieldLabel, Type) }
	 : {- empty -} { DL.empty }
	 | FieldTysNE { $1 }

FieldTysNE :: { DList (FieldLabel, Type) }
	   : FieldTy { DL.singleton $1 }
	   | FieldTysNE ',' FieldTy { DL.snoc $1 $3 }

FieldTy :: { (FieldLabel, Type) }
	: ID ':' Type { (fieldLabel $1, $3) }


Kind :: { Kind }
     : '*' { KiStar }

TyBind :: { (ID, Kind) }
       : '(' ID ':' Kind ')' { (ident $2, $4) }

{
data ParseError = EOF | ErrorAt Loc String

instance Show ParseError where
  show EOF = "unexpected EOF"
  show (ErrorAt l s) = s

parseError :: [L Token] -> Either ParseError a
parseError [] = Left EOF
parseError ts@(L l token:_) = Left $
  ErrorAt l $ "Parse Error:\n  " <> (intercalate "\n  " (show <$> take 5 ts))

ident :: L Token -> ID
ident (L _ (TokID s)) = ID s

fieldLabel :: L Token -> FieldLabel
fieldLabel (L _ (TokID s)) = FieldLabel s

int :: L Token -> Int
int (L _ (TokINT s)) = read s

string :: L Token -> String
string (L _ (TokSTRING s)) = read s -- remove initial/final quote and process escapes.

char :: L Token -> Char
char (L _ (TokCHAR s)) = case s of
  '\'':c:'\'':[] -> c
  '\'':'\\':'n':'\'':[] -> '\n'
  '\'':'\\':'t':'\'':[] -> '\t'
  '\'':'\\':'\\':'\'':[] -> '\\'
  '\'':'\\':'\'':'\'':[] -> '\''
  _ -> error "bad character" -- I need to handle escapes here too
}
