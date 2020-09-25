------ MODULE section_test ------

(*****************************************************************************)
(* Name: section_test                                                        *)
(* Author: Antoine Defourné                                                  *)
(* Date: 16/10/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

Surjective(f, A, B) ==
    /\ f \in [ A -> B ]
    /\ \A y \in B : \E x \in A : y = f[x]

THEOREM ASSUME NEW A, NEW B,
               NEW f \in [ A -> B ],
               Surjective(f, A, B)
        PROVE \E g \in [ B -> A ] : \A y \in B : f[g[y]] = y
<1> DEFINE g == [ y \in B |-> CHOOSE x \in A : y = f[x] ]
<1> DOMAIN g = B
    OBVIOUS
<1> \A y \in B : g[y] \in A /\ f[g[y]] = y
    BY DEF Surjective
<1> WITNESS g \in [ B -> A ]
<1> QED
    OBVIOUS

====

