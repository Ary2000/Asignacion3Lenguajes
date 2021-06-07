(* pruebas con constantes *)

val f = constante false
val t = constante true

val prop2 = f :=>: f :<=>: ~: f :||: f
val prop1 = f :=>: f :<=>: ~: f :=>: ~: f
;

val p = f;
val q = t;

val prop3 = p :=>: q :<=>: ~: p :||: q
val prop4 = p :=>: q :<=>: ~: q :=>: ~: p
;

(* pruebas *)

val pru1 = 	(variable "p") :=>: (variable "q") ;
val pru2 = (constante true) :=>: (variable "q") ;
val pru3 = (variable "p") :=>: ((variable "q") :=>: (variable "q")) ;
val pru4 = t :=>: f ;
val pru5 = f :=>: t ;

val vp = variable "p" ;
val vq = variable "q" ;

val pru6 = vp :&&: vq :=>: vq :||: vp ; (* SÍ es una tautología *)
val pru7 = vq :||: vp :=>: vp :&&: vq ; (* NO es una tautología *)
