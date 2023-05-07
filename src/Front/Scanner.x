{
{-# OPTIONS_HADDOCK prune #-}
module Front.Scanner 
	(
		Token(..), 
		alexScanTokens
	) where
}

%wrapper "basic"

$digit   = 0-9
$blank   = [\ \t]
@newline = [\n] | [\r][\n] | [\r]
@identifier = [a-zA-Z_] [a-zA-Z0-9_\']*

tokens :-
    "--".*    ;
    $blank+   ;
    @newline  ;
	"=="      {\s -> TokenTypeEq}
	let       {\s -> TokenLet}
	if     {\s -> TokenIf}
	then   {\s -> TokenThen}
	else   {\s -> TokenElse}
	Refl   {\s -> TokenRefl}
	subst  {\s -> TokenSubst}
	by     {\s -> TokenBy}
	\(     {\s -> TokenLP}
	\)     {\s -> TokenRP}
	\{     {\s -> TokenLB}
	\}     {\s -> TokenLB}
	\.     {\s -> TokenDot}
	\*     {\s -> TokenTimes}
	\|     {\s -> TokenLine}
	\,     {\s -> TokenComma}
	True   {\s -> TokenTrue}
	False  {\s -> TokenFalse}
	\\     {\s -> TokenSlash}
	\:     {\s -> TokenColon}
	\:\:   {\s -> TokenTypeDef}
	\;     {\s -> TokenSemicolon}
	\=     {\s -> TokenEqual}
    Type   {\s -> TokenUniverse}
	Unit   {\s -> TokenUnit}
	Bool   {\s -> TokenTBool}
	\-\>   {\s -> TokenArrow}
	@identifier {\s -> TokenId s}

{
-- Eacgh action has type :: String -> Token

-- The token type
data Token
	= TokenUniverse
	| TokenTBool
	| TokenTrue
	| TokenFalse
	| TokenLet
	| TokenUnit
	| TokenLB
	| TokenRB
	| TokenLP
	| TokenRP
	| TokenDot
	| TokenEqual
	| TokenId String
	| TokenSlash
	| TokenColon
	| TokenArrow
	| TokenIf
	| TokenThen
	| TokenElse
	| TokenTimes
	| TokenLine
	| TokenComma
	| TokenSemicolon
	| TokenIn
	| TokenTypeDef
	| TokenNL
	| TokenRefl
	| TokenTypeEq
	| TokenSubst
	| TokenBy
	deriving (Show)

main = do
  s <- getContents
  print (alexScanTokens s)
}