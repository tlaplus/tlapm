---- MODULE rangeisfinite_test ----

EXTENDS TLAPS, FiniteSets, Integers

THEOREM ASSUME NEW a \in Int,
               NEW b \in Int
        PROVE IsFiniteSet(a..b)
    OBVIOUS

====
