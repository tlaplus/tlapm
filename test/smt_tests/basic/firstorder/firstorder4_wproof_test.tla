------ MODULE firstorder4_test ------

(*****************************************************************************)
(* Name: firstorder4_test                                                    *)
(* Author: Antoine Defourné                                                  *)
(* Date: 15/07/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW D(_)
        PROVE \E x : D(x) => \A y : D(y)
<1>1 SUFFICES ASSUME \A x : D(x) /\ \E y : ~ D(y)
              PROVE FALSE
    OBVIOUS
<1>2 PICK y : ~ D(y)
    BY <1>1
<1>3 D(y)
    BY <1>1
<1> QED
    BY ONLY <1>2, <1>3

====

