------ MODULE set12_test ------

(*****************************************************************************)
(* Name: set12_test                                                          *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW A(_),
               NEW z
        PROVE \A x : x \in { y \in z : A(y) } <=> x \in z /\ A(x)
    OBVIOUS

====

