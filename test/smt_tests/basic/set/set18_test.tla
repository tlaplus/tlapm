------ MODULE set18_test ------

(*****************************************************************************)
(* Name: set18_test                                                          *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW S,
               S = { {} }
        PROVE \A x, y \in S : x = y
    OBVIOUS

====

