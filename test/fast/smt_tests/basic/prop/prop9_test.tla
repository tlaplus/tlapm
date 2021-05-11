------ MODULE prop9_test ------

(*****************************************************************************)
(* Name: prop9_test                                                          *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A \in BOOLEAN,
               NEW B \in BOOLEAN,
               NEW C \in BOOLEAN
        PROVE (A /\ B) => C <=> A => (B => C)
    OBVIOUS

====

