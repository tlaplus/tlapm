------ MODULE epsilon1_test ------

(*****************************************************************************)
(* Name: epsilon1_test                                                       *)
(* Author: Antoine Defourné                                                  *)
(* Date: 17/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW P(_),
               \E x : P(x)
        PROVE P(CHOOSE x : P(x))
    OBVIOUS

====

