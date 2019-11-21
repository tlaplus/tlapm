------ MODULE firstorder5_test ------

(*****************************************************************************)
(* Name: firstorder5_test                                                    *)
(* Author: Antoine Defourné                                                  *)
(* Date: 15/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW P(_),
               NEW a,
               NEW b
        PROVE \E x : P(x) => P(a) /\ P(b)
<1>1 CASE P(a) /\ P(b)
    BY <1>1
<1>2 CASE ~ P(a)
    BY <1>2
<1>3 CASE ~ P(b)
    BY <1>3
<1> QED
    BY ONLY <1>1, <1>2, <1>3

====

