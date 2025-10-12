---- MODULE GCD ----
EXTENDS Naturals
Divides(p, n) == \E q \in Nat : n = q * p
DivisorsOf(n) == { p \in Nat : Divides(p, n) }
SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j
GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
====
