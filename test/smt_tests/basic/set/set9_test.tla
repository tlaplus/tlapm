------ MODULE set9_test ------

(*****************************************************************************)
(* Name: set9_test                                                           *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM \A x, y, z : x \subseteq z /\ y \subseteq z => x \cup y \subseteq z
    OBVIOUS

====

