------------------------------- MODULE Euclid2 -------------------------------
(* A version of Euclid's program that allows one to test the algorithm for  *)
(* all pairs of values x0 \in 1 .. M, y0 \in 1 .. N.                        *)
(****************************************************************************)
EXTENDS Naturals

d | q == \E k \in 1..q : q = k*d
Divisors(q) == {d \in 1..q : d | q}
Maximum(S) == CHOOSE x \in S : \A y \in S : x >= y
GCD(p,q) == Maximum(Divisors(p) \cap Divisors(q))
PosInteger == Nat \ {0}

THEOREM GCDSelf == ASSUME NEW p \in PosInteger
                   PROVE  GCD(p,p) = p

THEOREM GCDSymm == ASSUME NEW p \in PosInteger, NEW q \in PosInteger
                   PROVE  GCD(p,q) = GCD(q,p)

THEOREM GCDDiff == ASSUME NEW p \in PosInteger, NEW q \in PosInteger, p < q
                   PROVE  GCD(p,q) = GCD(p,q-p)

-----------------------------------------------------------------------------

CONSTANTS M, N
ASSUME Positive == M \in PosInteger /\ N \in PosInteger
VARIABLES x, y, x0, y0

Init == /\ x0 \in 1 .. M /\ y0 \in 1 .. N
        /\ x = x0 /\ y = y0
Next == \/ /\ x < y
           /\ y' = y-x
           /\ x' = x
        \/ /\ y < x
           /\ x' = x - y
           /\ y' = y

vars == <<x,y,x0,y0>>
Spec == Init /\ [][Next /\ UNCHANGED <<x0,y0>>]_vars

-----------------------------------------------------------------------------

Correctness == x=y => x = GCD(x0,y0)
THEOREM Spec => []Correctness

=============================================================================
\* Modification History
\* Last modified Mon Oct 11 09:24:33 CEST 2010 by merz
\* Created Sat Oct 09 12:03:02 CEST 2010 by merz
