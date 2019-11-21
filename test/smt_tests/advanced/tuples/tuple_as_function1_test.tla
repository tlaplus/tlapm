------ MODULE tuple_as_function1_test ------

(*****************************************************************************)
(* Name: tuple_as_function1_test                                             *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS, Naturals

THEOREM ASSUME NEW A, NEW B, NEW C
        PROVE A \X B \X C \subseteq [ 1..3 -> UNION { A, B, C } ]
<1>1 SUFFICES ASSUME NEW x \in A \X B \X C
              PROVE x \in [ 1..3 -> UNION { A, B, C } ]
    OBVIOUS
<1>2 DOMAIN x = 1..3
    OBVIOUS
<1>3 \A i \in 1..3 : x[i] \in UNION { A, B, C }
    <2> TAKE i \in 1..3
    <2>1 i = 1 \/ i = 2 \/ i = 3    OBVIOUS
    <2>2 CASE i = 1     BY <2>2
    <2>3 CASE i = 2     BY <2>3
    <2>4 CASE i = 3     BY <2>4
    <2> QED
        BY ONLY <2>1, <2>2, <2>3, <2>4
<1> QED
    BY <1>2, <1>3
    
====

