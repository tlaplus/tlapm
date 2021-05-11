------ MODULE epsilon2_test ------

(*****************************************************************************)
(* Name: epsilon2_test                                                       *)
(* Author: Antoine Defourné                                                  *)
(* Date: 17/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW P(_), NEW S,
               \E x \in S : P(x)
        PROVE P(CHOOSE x \in S : P(x))
    OBVIOUS

====

