------ MODULE arith12_test ------

(*****************************************************************************)
(* Name: arith12_test                                                        *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS Integers, TLAPS

THEOREM \A m, n, p \in Int : m < n /\ n <= p => m < p
    OBVIOUS

====

