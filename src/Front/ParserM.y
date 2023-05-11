{
{-# OPTIONS_HADDOCK prune #-}
module Front.ParserM where

import Data.Char
import Front.Scanner
import Front.Ast
import Data.List (foldl')
import qualified Unbound.Generics.LocallyNameless as Unbound
}

%name calc program
%tokentype { Token }
%error { parseError }

%token
	'Type'     { TokenUniverse }
	'Bool'     { TokenTBool }
	'True'     { TokenTrue }
	'False'    { TokenFalse }
	'let'      { TokenLet }
	'Unit'     { TokenUnit }
	'if'       { TokenIf }
	'then'     { TokenThen }
	'else'     { TokenElse }
	'refl'     { TokenRefl}
	'('        { TokenLP }
	')'        { TokenRP }
	'='        { TokenEqual }
	'.'        { TokenDot }
	'\\'       { TokenSlash }
	'{'        { TokenLB }
	'}'        { TokenRB }
	':'        { TokenColon }
	'::'       { TokenTypeDef }
	'->'       { TokenArrow }
	'in'       { TokenIn }
	'*'        { TokenTimes }
	'|'        { TokenLine }
	','        { TokenComma }
	';'        { TokenSemicolon }
	'=='       { TokenTypeEq }
	'subst'    { TokenSubst}
	'by'       { TokenBy }
	'contra'   { TokenContra }
	-- newline    { TokenNL }
	Id         { TokenId $$ }


%nonassoc '=='

%%


program :
	 declas        { Program $1  }
   | {- empty -}   { Program []  }

declas :
	 declas decla  { $2:$1 }
   | decla         { [$1] }

decla :
      Id '::' term '.' { TypeSig (Sig {sigName = $1, sigType = $3}) }
    | Id '=' term  '.' { Def $1 $3 }


-- expr :
-- 	  term                                   { $1 }
-- 	-- | term '*' term                       { Sigma wildcard $1 $3 }


term :
	   ex                                     { $1 }
	 |  '\\' Id '.' term          		      { Lam $2 $4 }
	 | letExpr                                { $1 }
	 | ifExpr                                 { $1 }
	 | substExpr                              { $1 }
	 | contraExpr                             { $1 }
	 


ex :
      '(' Id ':' term ')' '->' ex        { PI $2 $4 $7 }
	| funapp '->' ex                     { PI "_" $1 $3 }
	| '(' Id ':' term '|' term ')'       { Sigma $2 $4 $6 }
	| '(' term '|' term ')'              { Sigma "_" $2 $4}
	| funapp                             { $1 }




funapp : 
	  funapp factor             { App $1 $2 }
	| factor                    { $1 }


factor : 
	  --expProdOrAnnotOrParens 			  { $1 }
	  Id                        		  { Var $1 }
	| '(' term ')'                        { $2 }
	| '(' term ',' term ')'               { Pair $2 $4 }
	| '(' term '==' term ')'              { TyEq $2 $4 }
	| bconst 							  { $1 }



letExpr : 'let' Id '=' term 'in' term               { Let $2 $4 $6 } 

ifExpr : 'if' term 'then' term 'else' term          { If $2 $4 $6 }

substExpr : 'subst' term 'by' term                  { Subst $2 $4 }

contraExpr : 'contra' term                              { Contra $2 }

bconst : 
		  'Unit'                                    { TUnit }
		| '(' ')'                                   { VUnit } 
		| 'Bool'                                    { TBool }
		| 'True'                                    { VBool True }
		| 'False'                                   { VBool False }
		| 'Type'                                    { Type }
		| 'refl'                                    { Refl }


afterBinder:
	  '->' term                           { $2 }


optional(p):
	  p { Just $1 }
	|   { Nothing}


afterColon:
    ':' term                             { $2 }

beforeBinder:
	   '(' term optional(afterColon) ')'            {% categorizeColon $2 $3 }

expProdOrAnnotOrParens:
	 beforeBinder optional(afterBinder)              {% categorize $1 $2 }
	
{

data InParens = Colon Term Term | Nope Term

parseError :: [Token] -> a
parseError tokens = error ("Parse error")

categorizeColon :: Term -> Maybe Term -> InParens
categorizeColon t Nothing = Nope t
categorizeColon t (Just t2) = Colon t t2

categorize :: InParens -> Maybe Term -> Term
categorize (Colon (Var x) a) (Just after) = PI x a after
categorize (Colon (Var x) a) Nothing = Ann (Var x) a
categorize (Colon a b) _ = Ann a b
-- categorize (Comma a b) _ = Prod a b
categorize (Nope a) _ = a


parse content = (calc . alexScanTokens) content
}



