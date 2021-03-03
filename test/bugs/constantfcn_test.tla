---- MODULE constantfcn_test ----

EXTENDS TLAPS

(* This is proved by SMT (Hernan Vanzetto's version) with `--debug types2`,
 * most likely because the domain condition is not checked in function
 * applications. *)

F == [ y \in { 1 } |-> 0 ]

THEOREM Thm1 ==
        F[0] = 0
    BY DEF F

(* Here is how this can be exploited to derive a contradiction.
 * It suffices to define functions F and G that are equal (same domain
 * and same values on that domain), but with expressions that do not
 * match for values outside their domain. *)

G == [ y \in { 1 } |-> IF y = 1 THEN 0 ELSE 1 ]

THEOREM Thm2 ==
        G[0] = 1
    (* Same method than Thm1 *)
    (*BY DEF G*)

THEOREM 0 = 1
<1>1 F = G    (*BY DEF F, G*)
<1>2 0 = F[0] (*BY Thm1*)
<1>3 @ = G[0] (*BY <1>1*)
<1>4 @ = 1    (*BY Thm2*)
<1> QED       (*BY ONLY <1>2, <1>3, <1>4*)

====
stderr: status:failed
