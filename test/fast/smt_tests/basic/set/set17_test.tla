------ MODULE set17_test ------

(*****************************************************************************)
(* Name: set17_test                                                          *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW S
        PROVE \A x, y \in S : x = y \/ x /= y
    OBVIOUS

====

