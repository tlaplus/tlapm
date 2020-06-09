------ MODULE zero_in_one_test ------

(*****************************************************************************)
(* Name: Zero In One                                                         *)
(* Author: Antoine Defourné                                                  *)
(*    a non-sensical formula.                                                *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS Integers, TLAPS

THEOREM 0 \in 1
    OBVIOUS

====
stretch: 1
stderr: status:failed
