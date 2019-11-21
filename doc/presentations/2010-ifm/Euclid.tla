------------------------------- MODULE Euclid -------------------------------
EXTENDS Naturals, TLAPS

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
VARIABLES x, y

Init == x = M /\ y = N
Next == \/ /\ x < y
           /\ y' = y-x
           /\ x' = x
        \/ /\ y < x
           /\ x' = x - y
           /\ y' = y

Spec == Init /\ [][Next]_<<x,y>>

-----------------------------------------------------------------------------

Correctness == x=y => x = GCD(M,N)
THEOREM Spec => []Correctness

InductiveInvariant == 
  /\ x \in PosInteger /\ y \in PosInteger
  /\ GCD(x,y) = GCD(M,N)
  
LEMMA InductiveInvariant => Correctness
BY GCDSelf DEF InductiveInvariant, Correctness

LEMMA Init => InductiveInvariant
BY Positive DEF Init, InductiveInvariant

LEMMA InductiveInvariant /\ [Next]_<<x,y>> => InductiveInvariant'
<1> USE DEFS InductiveInvariant, Next
<1> SUFFICES ASSUME InductiveInvariant, Next
             PROVE  InductiveInvariant'
  OBVIOUS
<1>a. CASE x < y
  <2>1. y-x \in PosInteger /\ ~(y<x)
    BY <1>a, SimpleArithmetic DEF PosInteger
  <2>2. QED
    BY <1>a, <2>1, GCDDiff
<1>b. CASE x > y
  <2>1. x-y \in PosInteger /\ ~(x<y)
    BY <1>b, SimpleArithmetic DEF PosInteger
  <2>2. GCD(y', x') = GCD(y, x)
    BY <1>b, <2>1, GCDDiff
  <2>3. QED
    BY <1>b, <2>1, <2>2, GCDSymm
<1>q. QED
  BY <1>a, <1>b             

=============================================================================
\* Modification History
\* Last modified Fri Nov 19 15:02:27 CET 2010 by merz
\* Created Sat Oct 09 12:03:02 CEST 2010 by merz
