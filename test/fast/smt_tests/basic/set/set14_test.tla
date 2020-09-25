------ MODULE set14_test ------

(*****************************************************************************)
(* Name: set14_test                                                          *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM \A x, y, z : x \in [y -> z] => DOMAIN x = y /\ \A s \in y : x[s] \in z
    OBVIOUS

====

