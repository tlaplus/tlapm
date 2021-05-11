------ MODULE firstorder4_test ------

(*****************************************************************************)
(* Name: firstorder4_test                                                    *)
(* Author: Antoine Defourné                                                  *)
(* Date: 15/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW D(_)
        PROVE \E x : D(x) => \A y : D(y)
    OBVIOUS

====

