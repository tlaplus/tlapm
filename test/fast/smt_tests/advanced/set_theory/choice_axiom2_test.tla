------ MODULE choice_axiom2_test ------

(*****************************************************************************)
(* Name: choice_axiom2_test                                                  *)
(* Author: Antoine Defourné                                                  *)
(* Date: 16/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

THEOREM ASSUME NEW I, NEW X,
               NEW a \in [ I -> X ],
               \A i \in I : a[i] /= {}
        PROVE LET Y == UNION { a[i] : i \in I } IN
              { f \in [ I -> Y ] : \A i \in I : f[i] \in a[i] }
              /= {}
<1> DEFINE Y == UNION { a[i] : i \in I }
<1> SUFFICES \E f \in [ I -> Y ] : \A i \in I : f[i] \in a[i]
    OBVIOUS
<1> DEFINE f == [ i \in I |-> CHOOSE x \in a[i] : x = x ]
<1> \A i \in I : f[i] \in a[i]
    OBVIOUS
<1> WITNESS f \in [ I -> Y ]
<1> QED
    OBVIOUS

====

