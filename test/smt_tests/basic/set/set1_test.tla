------ MODULE set1_test ------

(*****************************************************************************)
(* Name: set1_test                                                           *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM \A x, y : x \subseteq y => \A z : z \in x => z \in y
    OBVIOUS

====

