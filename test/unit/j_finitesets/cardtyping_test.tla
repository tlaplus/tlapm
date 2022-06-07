---- MODULE cardtyping_test ----

EXTENDS TLAPS, FiniteSets, Naturals

THEOREM ASSUME NEW x,
               IsFiniteSet(x)
        PROVE Cardinality(x) \in Nat
    OBVIOUS

====
