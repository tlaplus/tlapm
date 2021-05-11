------ MODULE prop5_test ------

(*****************************************************************************)
(* Name: prop5_test                                                          *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A \in BOOLEAN
        PROVE FALSE => A
    OBVIOUS

====

