------ MODULE epsilon3_test ------

(*****************************************************************************)
(* Name: epsilon3_test                                                       *)
(* Author: Antoine Defourné                                                  *)
(* Date: 18/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW P(_),
               ~ P(CHOOSE x : P(x))
        PROVE \A x : ~ P(x)
    OBVIOUS

====

