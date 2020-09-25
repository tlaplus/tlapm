------ MODULE epsilon4_test ------

(*****************************************************************************)
(* Name: epsilon4_test                                                       *)
(* Author: Antoine Defourné                                                  *)
(* Date: 18/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW P(_), NEW S,
               ~ P(CHOOSE x \in S : P(x))
        PROVE \A x \in S : ~ P(x)
    OBVIOUS

====

