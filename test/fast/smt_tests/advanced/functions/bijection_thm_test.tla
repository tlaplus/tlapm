------ MODULE bijection_thm_test ------

(*****************************************************************************)
(* Name: bijection_thm_test                                                  *)
(* Author: Antoine Defourné                                                  *)
(* Date: 25/09/19                                                            *)
(*****************************************************************************)

EXTENDS TLAPS

IsId(f) == \A x \in DOMAIN f : f[x] = x

g \o f == [ x \in DOMAIN f |-> g[f[x]] ]

Injective(f, A, B) ==
    /\ f \in [ A -> B ]
    /\ \A x, y \in A : f[x] = f[y] => x = y

Surjective(f, A, B) ==
    /\ f \in [ A -> B ]
    /\ \A z \in B : \E x \in A : f[x] = z

Bijective(f, A, B) ==
    /\ f \in [ A -> B ]
    /\ \E g \in [ B -> A ] : IsId(f \o g) /\ IsId(g \o f)

THEOREM ASSUME NEW A,
               NEW B,
               NEW f \in [ A -> B ]
        PROVE Injective(f,
        A, B) /\ Surjective(f, A, B) <=> Bijective(f, A, B)

<1>1 ASSUME Injective(f, A, B),
            Surjective(f, A, B)
     PROVE Bijective(f, A, B)
    <2>1 \A y \in B : \E x \in A : f[x] = y
        BY <1>1 DEF Surjective
    <2> DEFINE g == [ y \in B |-> CHOOSE x \in A : f[x] = y ]
    <2>2 \A y \in B : \A x \in A : f[x] = y => x = g[y]
        BY <1>1 DEF Injective
    <2>3 IsId(f \o g)
        BY <2>1 DEF IsId, \o
    <2>4 IsId(g \o f)
        BY <2>2 DEF IsId, \o
    <2> QED
        BY <2>1, <2>3, <2>4 DEF Bijective

<1>2 ASSUME Bijective(f, A, B)
     PROVE Injective(f, A, B) /\ Surjective(f, A, B)
    <2>1 PICK g \in [ B -> A ] : IsId(f \o g) /\ IsId(g \o f)
        BY <1>2 DEF Bijective
    <2>2 Injective(f, A, B)
        <3>1 SUFFICES ASSUME NEW x \in A,
                             NEW y \in A,
                             f[x] = f[y]
                      PROVE x = y
            BY DEF Injective
        <3>2 x = (g \o f)[x]    BY <2>1 DEF IsId, \o
        <3>3 @ = g[ f[x] ]      BY DEF \o
        <3>4 @ = g[ f[y] ]      BY <3>1
        <3>5 @ = (g \o f)[y]    BY DEF \o
        <3>6 @ = y              BY <2>1 DEF IsId, \o
        <3> QED
            BY ONLY <3>2, <3>3, <3>4, <3>5, <3>6
    <2>3 Surjective(f, A, B)
        <3>1 SUFFICES ASSUME NEW y \in B
                      PROVE \E x \in A : f[x] = y
            BY DEF Surjective
        <3>2 WITNESS g[y] \in A
        <3> QED
            BY <2>1 DEF IsId, \o
    <2> QED
        BY ONLY <2>2, <2>3

<1> QED
    BY ONLY <1>1, <1>2

====

