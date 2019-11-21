------ MODULE set10_test ------

(*****************************************************************************)
(* Name: set10_test                                                          *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM \A x, y : x \in UNION y <=> \E z \in y : x \in z
    OBVIOUS

====

