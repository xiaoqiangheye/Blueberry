Blueberry-A dependently typed language

-build the program by
		stack build


-test the program by
		stack exec blueberry-exe test.pi


-Syntax
program : declaration*
declaration : 
	  id :: term .      —type signature
	 | id = term .     —definition

term : exp  —expression
       | \ id . term    —Lambda expression
       | let id = term in term  —Let expression
       | If term then term else term  —If expression
	   | Subst term by term    -Subst expression

exp : ( id : term ) -> exp    -PI
        | term -> exp            -PI with no binder
        | ( id : term | term )    -Sigma
        | ( term | term )         -Sigma with no binder
        | funapp

funapp : funapp factor       -application
            | factor

factor : Id | ( term ) | const


const : Unit  	    -Type Unit
        ()    		-Unit value
        Bool 	    -Bool Type
        True 	    -VBool True
        False 	    -VBool True
        Type 	    -Type
		Refl        -Refl