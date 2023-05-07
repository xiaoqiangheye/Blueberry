# Blueberry-A dependently typed language

## build the program by
	stack build


## test the program by
	stack exec blueberry-exe test.pi


## Syntax

- program : declaration*

- declaration : **id** :: **term** .  | **id** '=' **term** .

- term : **exp**
       | \ **id** . **term**
       | let **id** = **term** in **term**
       | If **term** then **term** else **term**
       | Subst **term** by **term**

- exp : ( id : **term** ) -> **exp**
        | **term** -> **exp**
        | ( **id** : **term** | **term** )
        | ( **term** | **term** )
        | **funapp**

- funapp : **funapp** **factor**
          | **factor**

- factor : **Id** | ( **term** ) | **const**


- const : Unit | () | Bool | True | False | Type | Refl      
