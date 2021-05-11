------ MODULE firstorder6_test ------

(*****************************************************************************)
(* Name: firstorder6_test                                                    *)
(* Author: Antoine Defourné                                                  *)
(* Date: 15/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW P(_, _),
               \E x : \A y : P(x, y)
        PROVE \A z : \E w : P(w, z)
    OBVIOUS

====

