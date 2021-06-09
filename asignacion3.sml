use "codigo/sintax.sml";

val pru5 = conjuncion(implicacion(conjuncion(variable "a", variable "b"),
                           conjuncion(variable "x", variable "y")),
               conjuncion(negacion(conjuncion(variable "a", variable "b")),
                          disyuncion(variable "x", variable "y")));
val p=variable "p" and q=variable "q";
val pru6 = (p :=>: ~:q ) :&&: ~:(~:q :=>: p);
fun bonita prop =
	let 
		fun discriminante (prop,importancia) = case prop of 
					conjuncion (_,_) =>importancia>1
				|	disyuncion (_,_) =>importancia>2
				|	implicacion (_,_) =>importancia>3
				|	equivalencia (_,_) =>importancia>4
				|	_=>false 		
	in
		case prop of
			constante false             => "false"
		|   constante true              => "true"
		|   variable nombre             => nombre
		|   negacion prop1              => let
			val izq = discriminante (prop1, 4)
			in
				"~" ^ (if izq then "("else "") ^ bonita  prop1 ^ (if izq then ")" else "")
			end
		|   conjuncion (prop1,prop2)	=> let
			val izq = discriminante (prop1, 1) and der = discriminante (prop2, 1)
			in 
				(if izq then "("else "") ^ bonita prop1 ^ (if izq then ")"else "") ^ 
				" \\/ "^ (if der then "("else "") ^ bonita prop2 ^ (if der then ")"else "")
			end
		|   disyuncion (prop1,prop2)	=> let
			val izq = discriminante (prop1,2) and der = discriminante (prop2,2)
			in 
				(if izq then "("else "") ^ bonita prop1 ^ (if izq then ")"else "") ^ 
				" /\\ "^ (if der then "("else "") ^ bonita prop2 ^ (if der then ")"else "")
			end
		|   implicacion (prop1,prop2)	=> let
			val izq = discriminante (prop1,3) and der = discriminante (prop2,3)
			in 
				(if izq then "("else "") ^ bonita prop1 ^ (if izq then ")"else "") ^ 
				" => "^ (if der then "("else "") ^ bonita prop2 ^ (if der then ")"else "")
			end
		|   equivalencia (prop1,prop2)	=> let
			val izq = discriminante (prop1,4) and der = discriminante (prop2,4)
			in 
				(if izq then "("else "") ^ bonita prop1 ^ (if izq then ")"else "") ^ 
				" <=> "^ (if der then "("else "") ^ bonita prop2 ^ (if der then ")"else "")
			end
	end
;

fun simpl prop =
	case prop 
	of	implicacion(prop1,prop2)=>conjuncion(simpl (negacion prop1),simpl prop2)
	|	negacion (negacion prop1)=>simpl prop1
	|	negacion (conjuncion(prop1,prop2))=>disyuncion(simpl (negacion prop1),simpl (negacion prop2))
	| 	negacion (disyuncion(prop1,prop2))=>conjuncion(simpl (negacion prop1),simpl (negacion prop2))
	|	negacion (implicacion(prop1,prop2))=>disyuncion(simpl prop1,simpl (negacion prop2))
	|	conjuncion(prop1,prop2)=>
		let val simProp1=simpl prop1 and simProp2=simpl prop2
		in if simProp1=simProp2 then simProp1 else 
			case simProp1 
			of 	disyuncion(pp1,pp2)=>
				let val v = case simProp2 
					of  conjuncion(pp3,pp4)=>
							if pp3=pp1 andalso pp4=pp2 orelse pp3=pp2 andalso pp4=pp1 
							then conjuncion(pp3,pp4)
							else conjuncion(simProp1,simProp2)
					|	_=>conjuncion(simProp1,simProp2)
				in v end
			|	conjuncion(pp3,pp4)=>
				let val v =	case simProp2 
					of	disyuncion(pp1,pp2)=>
							if pp3=pp1 andalso pp4=pp2 orelse pp3=pp2 andalso pp4=pp1 
							then conjuncion(pp3,pp4)
							else conjuncion(simProp1,simProp2)
					|	_=> conjuncion(simProp1,simProp2)
				in v end
			|	_=> conjuncion(simProp1,simProp2) 
		end
	|	disyuncion(prop1,prop2)=>
		let val simProp1=simpl prop1 and simProp2=simpl prop2
		in if simProp1=simProp2 then simProp1 else  
			case simProp1 
			of 	disyuncion(pp1,pp2)=>
				let val v = case simProp2 
					of	conjuncion(pp3,pp4)=>
							if pp3=pp1 andalso pp4=pp2 orelse pp3=pp2 andalso pp4=pp1 
							then disyuncion(pp3,pp4)
							else disyuncion(simProp1,simProp2)
					|	_=>disyuncion(simProp1,simProp2)
				in v end
			|	conjuncion(pp3,pp4)=>
				let val v = case simProp2 
					of	disyuncion(pp1,pp2)=>
							if pp3=pp1 andalso pp4=pp2 orelse pp3=pp2 andalso pp4=pp1 
							then disyuncion(pp3,pp4)
							else disyuncion(simProp1,simProp2)
					|	_=>disyuncion(simProp1,simProp2)
				in v end
			|	_=> disyuncion(simProp1,simProp2) 
		end
	|	_=>prop
;

fun filter p []      = []
|   filter p (x::xs) = if p x then x :: filter p xs else filter p xs
;

fun revisarTipo prop =
    case prop of
        disyuncion(_,_)
            => true
    |   _ => false
    ;


fun distribucionDoble (disyuncion(var1, var2), disyuncion(var3, var4)) =
    disyuncion(conjuncion(var1, var3), conjuncion(var2, var4))
    ;

fun distribucionSimple (disyuncion(vars1, vars2), prop2) =
    disyuncion(conjuncion(vars1, prop2), conjuncion(vars2, prop2))
    ;

(*fnd(conjuncion(disyuncion(variable "a", variable "b"), disyuncion(variable "c", variable "d")));*)

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