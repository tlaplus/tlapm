------ MODULE firstorder5_test ------

(*****************************************************************************)
(* Name: firstorder5_test                                                    *)
(* Author: Antoine Defourné                                                  *)
(* Date: 15/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW P(_),
               NEW a,
               NEW b
        PROVE \E x : P(x) => P(a) /\ P(b)
    OBVIOUS

====

