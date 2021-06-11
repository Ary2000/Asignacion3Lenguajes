(* Imprimir la tabla de verdad de una proposición con variables *)
fun FND prop =
    let
      (* variables de trabajo *)
      val variables = vars prop
      val n = length variables
      val lista_combinaciones_booleanas = gen_bools n
	  (*val lista_trues = recorrerFND lista_combinaciones_booleanas*)
      (* generar evaluaciones de la proposición*)
	  fun devolverVariable (var, bool) = 
	  	if bool then variable(var) else negacion(variable(var))
		  ;
      fun recorrerFND []                  = []  (* toque final a la impresión; previamente mostramos hileras con el resultado *)
    |   recorrerFND (fila :: mas_filas) = 
            let
                val asociacion = as_vals variables fila
				val resultados = recorrerFND mas_filas
				val resultadoActual = evalProp asociacion prop
				val respuesta = map devolverVariable asociacion
                in
                  if resultadoActual = true then 
				  	respuesta::resultados 
				  else 
				  	resultados
              end
      fun gc [] = constante(false)
      |   gc [x] = x
      |   gc (x::y::resto) = conjuncion(x, gc(y::resto))
      fun gd [] = constante(true)
      |   gd [x] = x
      |   gd (x::y::resto) = disyuncion(x, gd(y::resto))
      val lista_trues = recorrerFND lista_combinaciones_booleanas
      val lista_conjunciones = map gc(lista_trues)
    in
        gd lista_conjunciones
    end
;