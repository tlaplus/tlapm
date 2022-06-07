---- MODULE singletonisfinite_test ----

EXTENDS TLAPS, FiniteSets

THEOREM ASSUME NEW a
        PROVE IsFiniteSet({ a })
    OBVIOUS

====
