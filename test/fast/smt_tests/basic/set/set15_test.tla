------ MODULE set15_test ------

(*****************************************************************************)
(* Name: set15_test                                                          *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW S,
               \A y \in S : { x \in S : x /= y } /= {},
               \A z, y \in S : { x \in S : x /= y } /= {}
        PROVE S = S
    OBVIOUS

====

