------ MODULE set19_test ------

(*****************************************************************************)
(* Name: set19_test                                                          *)
(* Author: Antoine Defourné                                                  *)
(* Date: 16/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW S
        PROVE S \subseteq { x \in S : x \in S }
    OBVIOUS

====

