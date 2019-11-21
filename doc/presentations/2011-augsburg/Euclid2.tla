------------------------------- MODULE Euclid2 -------------------------------
(* A version of Euclid's program that allows one to test the algorithm for  *)
(* all pairs of values x0 \in 1 .. M, y0 \in 1 .. N.                        *)
(****************************************************************************)
EXTENDS Naturals

PosInteger == Nat \ {0}
Maximum(S) == CHOOSE x \in S : \A y \in S : x >= y

d | q == \E k \in 1..q : q = k*d
Divisors(q) == {d \in 1..q : d | q}
GCD(p,q) == Maximum(Divisors(p) \cap Divisors(q))

-----------------------------------------------------------------------------

CONSTANT M
ASSUME Positive == M \in PosInteger
VARIABLES x, y, x0, y0

Init == /\ x0 \in 1 .. M /\ y0 \in 1 .. M
        /\ x = x0 /\ y = y0
SubX == x < y /\ y' = y-x /\ UNCHANGED <<x, x0, y0>>
SubY == y < x /\ x' = x - y /\ UNCHANGED <<y, x0, y0>>

vars == <<x,y,x0,y0>>
Spec == Init /\ [][SubX \/ SubY]_vars /\ WF_vars(SubX \/ SubY)

-----------------------------------------------------------------------------

Correctness == x=y => x = GCD(x0,y0)
THEOREM Spec => []Correctness

=============================================================================
\* Modification History
\* Last modified Thu Feb 10 16:35:14 CET 2011 by merz
\* Created Sat Oct 09 12:03:02 CEST 2010 by merz
