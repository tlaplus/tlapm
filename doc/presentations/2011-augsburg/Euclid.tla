------------------------------- MODULE Euclid -------------------------------
EXTENDS Naturals, TLAPS

PosInteger == Nat \ {0}
Maximum(S) == CHOOSE x \in S : \A y \in S : x >= y

d | q == \E k \in 1..q : q = k*d
Divisors(q) == {d \in 1..q : d | q}
GCD(p,q) == Maximum(Divisors(p) \cap Divisors(q))

-----------------------------------------------------------------------------

CONSTANTS M, N
ASSUME Positive == M \in PosInteger /\ N \in PosInteger
VARIABLES x, y

Init == x = M /\ y = N
SubX == x < y /\ y' = y-x /\ x' = x
SubY == y < x /\ x' = x - y /\ y' = y

Spec == Init /\ [][SubX \/ SubY]_<<x,y>>

-----------------------------------------------------------------------------

Correctness == x=y => x = GCD(M,N)
Termination == <>(x = y)

InductiveInvariant ==
  /\ x \in PosInteger /\ y \in PosInteger
  /\ GCD(x,y) = GCD(M,N)

(* Data properties that we leave unproved *)
THEOREM GCDSelf == ASSUME NEW p \in PosInteger
                   PROVE  GCD(p,p) = p

THEOREM GCDSymm == ASSUME NEW p \in PosInteger, NEW q \in PosInteger
                   PROVE  GCD(p,q) = GCD(q,p)

THEOREM GCDDiff == ASSUME NEW p \in PosInteger, NEW q \in PosInteger, p < q
                   PROVE  GCD(p,q) = GCD(p,q-p)

LEMMA InductiveInvariant => Correctness
BY GCDSelf DEFS InductiveInvariant, Correctness

LEMMA Init => InductiveInvariant
BY Positive DEFS Init, InductiveInvariant

LEMMA InductiveInvariant /\ [SubX \/ SubY]_<<x,y>> => InductiveInvariant'
<1> USE DEFS InductiveInvariant
<1>1. ASSUME InductiveInvariant, SubX
      PROVE  InductiveInvariant'
  <2>1. x' \in PosInteger /\ y' \in PosInteger
    BY <1>1, SimpleArithmetic DEFS SubX, PosInteger
  <2>2. QED
    BY <1>1, <2>1, GCDDiff DEF SubX
<1>2. ASSUME InductiveInvariant, SubY
      PROVE  InductiveInvariant'
  <2>1. x' \in PosInteger /\ y' \in PosInteger
    BY <1>2, SimpleArithmetic DEFS SubY, PosInteger
  <2>2. QED
    BY <1>2, <2>1, GCDDiff, GCDSymm DEF SubY
<1>q. QED
  BY <1>1, <1>2


=============================================================================
\* Modification History
\* Last modified Mon Apr 11 22:06:15 CEST 2011 by merz
\* Created Sat Oct 09 12:03:02 CEST 2010 by merz
