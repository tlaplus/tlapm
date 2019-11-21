------ MODULE cantor1_test ------

(*****************************************************************************)
(* Name: cantor1                                                             *)
(* Author: Antoine Defourné                                                  *)
(* Date: 12/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

Surjective(f, A, B) ==
            /\ f \in [ A -> B ]
            /\ \A y \in B : \E x \in A : f[x] = y

THEOREM \A E : ~ \E f : Surjective(f, E, SUBSET E)
<1>1 SUFFICES ASSUME NEW E,
                     NEW f \in [ E -> SUBSET E ],
                     \A P \in SUBSET E : \E x \in E : f[x] = P
              PROVE FALSE
    BY DEF Surjective
<1> DEFINE D == { x \in E : x \notin f[x] }
<1> D \in SUBSET E
    OBVIOUS
<1>2 PICK d \in E : f[d] = D
    BY <1>1
<1>3 d \in f[d] <=> d \in D
    BY <1>2
<1>4          @ <=> d \notin f[d]
    OBVIOUS
<1> QED
    BY ONLY <1>3, <1>4

====

