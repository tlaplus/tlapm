------ MODULE set8_test ------

(*****************************************************************************)
(* Name: set8_test                                                           *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM \A x, y, z : z \subseteq x /\ z \subseteq y => z \subseteq x \cap y
    OBVIOUS

====

