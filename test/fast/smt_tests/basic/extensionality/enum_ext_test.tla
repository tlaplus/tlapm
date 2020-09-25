------ MODULE mytest_test ------

(*****************************************************************************)
(* Name: mytest_test                                                         *)
(* Author: Antoine Defourné                                                  *)
(* Date: 01/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW x, NEW y, NEW S,
               \A z : z \in S <=> z = x \/ z = y
        PROVE S = {x, y}
    OBVIOUS

====

