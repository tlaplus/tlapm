------ MODULE firstorder3_test ------

(*****************************************************************************)
(* Name: firstorder3_test                                                    *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW P(_, _),
               NEW f(_),
               \A x : P(x, f(x))
        PROVE \A x : \E y : P(x, y)
<1> TAKE x
<1> WITNESS f(x)
<1> QED
    OBVIOUS

====

