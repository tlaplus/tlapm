---- MODULE subsetisfinite_test ----

EXTENDS TLAPS, FiniteSets

THEOREM ASSUME NEW a,
               IsFiniteSet(a)
        PROVE IsFiniteSet(SUBSET a)
    OBVIOUS

====
