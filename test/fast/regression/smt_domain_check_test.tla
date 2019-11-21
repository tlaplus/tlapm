---- MODULE smt_domain_check_test ----
EXTENDS Naturals, Integers, TLAPS
LEMMA
 ASSUME NEW N \in Nat,
        NEW f \in [0 .. N-1 -> Int]
 PROVE  \A i \in Nat : (IF i < N THEN f[i] ELSE 42) \in Int
BY SMT
====
