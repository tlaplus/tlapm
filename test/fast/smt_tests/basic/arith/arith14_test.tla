------ MODULE arith14_test ------

(*****************************************************************************)
(* Name: arith14_test                                                        *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS Integers, TLAPS

THEOREM \A m, n, p \in Int : (m + n) * p = (m * p) + (n * p)
    OBVIOUS

====

