------ MODULE one_div_zero_test ------

(*****************************************************************************)
(* Name: one_div_zero                                                        *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS, Integers

THEOREM 1 \div 0 \in Int
    OBVIOUS

====
stderr: status:failed
