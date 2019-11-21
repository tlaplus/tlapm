------ MODULE prop3_test ------

(*****************************************************************************)
(* Name: prop3_test                                                          *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A \in BOOLEAN
        PROVE ~ ~ A <=> A
    OBVIOUS

====

