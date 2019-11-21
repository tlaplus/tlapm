------ MODULE set13_test ------

(*****************************************************************************)
(* Name: set13_test                                                          *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW E(_),
               NEW z
        PROVE \A x : x \in { E(y) : y \in z } <=> \E y \in z : x = E(y)
    OBVIOUS

====

