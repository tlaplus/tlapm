------ MODULE arith13_test ------

(*****************************************************************************)
(* Name: arith13_test                                                        *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS Integers, TLAPS

THEOREM \A m, n \in Int : m <= n /\ m >= n => m = n
    OBVIOUS

====

