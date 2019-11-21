------ MODULE prop8_test ------

(*****************************************************************************)
(* Name: prop8_test                                                          *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A \in BOOLEAN,
               NEW B \in BOOLEAN
        PROVE ~ (A \/ B) <=> ~ A /\ ~ B
    OBVIOUS

====

