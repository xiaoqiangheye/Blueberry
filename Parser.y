{


}

%name parse
%tokenType { Token }

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
	'('        { TokenLP }
	')'        { TokenRP }
	'='        { TokenEqual }
	'.'        { TokenDot }
	'\\'       { TokenSlash }
	'{'        { TokenLB }
	'}'        { TokenRB }
	':'        { TokenColon }
	'->'       { TokenArrow }
	'in'       { TokenIn }
	'*'        { TokenTimes }
	'|'        { TokenLine }
	','        { TokenComma }
	';'        { TokenSemicolon }
	Id         { TokenId $$ }


%%


program : Id        { $1 }


-- declas :
-- 	decla ';' declas   {[$1 : $2]}


-- decla :
--       Id ':' term  { Sig {sigName = $1, sigType = $3} }
--     | Id '=' term  { Def $1 $3 }



-- termAtom :
-- 	  Type                     				{ Type }
-- 	| Id                        			{ Var $1 }

	-- | '(' term ')'                          { $1 }

-- termApp :
-- 	  termApp termAtom                     { App $1 $2 }
--     | termAtom                             { $1 }

-- term :
-- 	 '\\' Id '.' term          		{ Lam $2 $4 }
-- 	| termApp                       { $1 }
	
-- term
-- 	: Id '.' term {Lam $1 $3}
	
-- | '(' Id ':' term ')'            		{ Ann $2 $4}
	-- | '(' term ')'        					{ $2 }
	-- | 'let' Id '=' term 'in' term           { Let $2 $4 $6}
	-- | 'Unit'                                { TUnit }
	-- | '(' ')'                               { VUnit } 
	-- | 'Bool'                                { TBool }
	-- | 'True'                                { VBool True }
	-- | 'False'                               { VBool False }
	-- | 'if' term 'then' term 'else' term     { If $2 $4 $6}
	-- | '{' Id ':' term  '|' term '}'         { TDPair $2 $4 $6}
	-- | term '*' term                         { TNPair $1 $3 }
	-- | pair                                  { $1 }
	-- | 'let' pair '=' term 'in' term         { LetPair $2 $4 $6}
	

-- pair :
-- 	'(' Id ',' Id ')'                       { VPair $2 $4 }
{
happyError :: [Token] -> a
happyError _ = error ("Parse error\n")

runParser :: String -> Term
runParser :: parse . alexScanTokens

main :: IO ()
main = getContents >>= print . parse . alexScanTokens
}