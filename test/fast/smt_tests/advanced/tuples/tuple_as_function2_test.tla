------ MODULE tuple_as_function2_test ------

(*****************************************************************************)
(* Name: tuple_as_function2_test                                             *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS, Naturals

THEOREM ASSUME NEW A, NEW B,
               A /= B
        PROVE A \X B /= [ 1..2 -> A \cup B ]
<1>1 CASE A = {} /\ B = {}
    BY <1>1
<1>2 CASE A /= {} \/ B /= {}
    <2>1 A \cup B /= {}
        BY <1>2
    <2>2 PICK x \in A \cup B :
            \/ x \in A \ B
            \/ x \in B \ A
        BY <1>2, <2>1
    <2> DEFINE f == [ i \in 1..2 |-> x ]
    <2>3 f \in [ 1..2 -> A \cup B ]
        OBVIOUS
    <2>4 f \notin A \X B
        <3>1 CASE x \in A \ B
            <4>1 f[2] \notin B  BY <3>1
            <4> QED             BY <4>1
        <3>2 CASE x \in B \ A
            <4>1 f[1] \notin A  BY <3>2
            <4> QED             BY <4>1
        <3> QED
            BY ONLY <2>2, <3>1, <3>1
    <2> QED
        BY ONLY <2>3, <2>4
<1> QED
    BY ONLY <1>1, <1>2

====

