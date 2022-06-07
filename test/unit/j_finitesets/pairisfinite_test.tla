---- MODULE pairisfinite_test ----

EXTENDS TLAPS, FiniteSets

THEOREM ASSUME NEW a,
               NEW b
        PROVE IsFiniteSet({ a, b })
    OBVIOUS

====
