fun fnd prop [] = []
|   fnd prop(x::xs) = if

fun filter p []      = []
|   filter p (x::xs) = if p x then x :: filter p xs else filter p xs
;

fun revisarTipo prop =
    case prop of
        disyuncion(_,_)
            => true
    |   _ => false
    ;

fun revisarNegacion

fun distribucionDoble (disyuncion(var1, var2), disyuncion(var3, var4)) =
    disyuncion(conjuncion(var1, var3), conjuncion(var2, var4))
    ;

fun distribucionSimple (disyuncion(vars1, vars2), prop2) =
    disyuncion(conjuncion(vars1, prop2), conjuncion(vars2, prop2))
    ;

fnd(conjuncion(disyuncion(variable "a", variable "b"), disyuncion(variable "c", variable "d")));

fun fnd prop =
	  case prop of
	    constante var
	       => constante var
      | variable var
	       => variable var
	  | negacion prop1
	       => let val vars = fnd prop1
           in case vars of 
           negacion prop1 => prop1
           | _ => negacion(vars)
           end
	  | conjuncion (prop1, prop2)
	       => let val vars1 = fnd prop1
	              and vars2 = fnd prop2
	          in 
                if revisarTipo vars1 = true then
                    if revisarTipo vars2 = true then
                        distribucionDoble(vars1, vars2)
                    else
                        distribucionSimple(vars1, vars2)
                else 
                    if revisarTipo vars2 = true then
                        distribucionSimple(vars2, vars1)
                    else
                     conjuncion(vars1, vars2)
	          end
	  | disyuncion (prop1, prop2)
	       => let val vars1 = fnd prop1
	              and vars2 = fnd prop2
	          in  disyuncion(vars1, vars2)
	          end
	  | implicacion (prop1, prop2)
	       => let val vars1 = fnd prop1
	              and vars2 = fnd prop2
	          in  disyuncion(negacion(vars1), vars2)
	          end
	  | equivalencia (prop1, prop2)
	       => let val vars1 = fnd prop1
	              and vars2 = fnd prop2
	          in  conjuncion(disyuncion(negacion(vars1), vars2), disyuncion(negacion(vars2), vars1))
	          end
              ;