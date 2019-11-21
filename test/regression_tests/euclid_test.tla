-------------------- MODULE euclid_test --------------------
EXTENDS Integers, TLAPS

p | q == \E d \in 1..q : q = p * d
Divisors(q) == {d \in 1..q : d | q}
Maximum(S) == CHOOSE x \in S : \A y \in S : x \geq y
GCD(p,q) == Maximum(Divisors(p) \cap Divisors(q))
Number == Nat \ {0}

CONSTANTS M, N
VARIABLES x, y

Init == (x = M) /\ (y = N)

Next == \/ /\ x < y
           /\ y' = y - x
           /\ x' = x
        \/ /\ y < x
           /\ x' = x-y
           /\ y' = y

Spec == Init /\ [][Next]_<<x,y>>

ResultCorrect == (x = y) => x = GCD(M, N)

InductiveInvariant == /\ x \in Number
                      /\ y \in Number
                      /\ GCD(x, y) = GCD(M, N)

ASSUME NumberAssumption == M \in Number /\ N \in Number

THEOREM InitProperty == Init => InductiveInvariant
  BY NumberAssumption DEF Init, InductiveInvariant

AXIOM GCDProperty1 == \A p \in Number : GCD(p, p) = p
AXIOM GCDProperty2 == \A p, q \in Number : GCD(p, q) = GCD(q, p)
AXIOM GCDProperty3 == \A p, q \in Number : (p < q) => GCD(p, q) = GCD(p, q-p)

THEOREM NextProperty == InductiveInvariant /\ Next => InductiveInvariant'
<1> SUFFICES ASSUME InductiveInvariant, Next
             PROVE  InductiveInvariant'
  OBVIOUS
<1> USE DEF InductiveInvariant, Next
<1>1. (x < y) \/ (y < x)
  OBVIOUS
<1>a. CASE x < y
  <2>1. (y - x \in Number) /\ ~(y < x)
    BY <1>a, SMT DEF Number
  <2>2. QED
    BY <1>a, <2>1, GCDProperty3
<1>b. CASE y < x
  <2>1. (x - y \in Number) /\ ~(x < y)
    BY <1>b, SMT DEF Number
  <2>2. GCD(y', x') = GCD(y, x)
    BY <1>b, <2>1, GCDProperty3
  <2>4. QED
    BY <1>b, <2>1, <2>2, GCDProperty2
<1>2. QED
  BY <1>1, <1>a, <1>b

THEOREM Correctness == Spec => []ResultCorrect

=======================================================
