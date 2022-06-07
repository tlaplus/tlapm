---- MODULE setminusisfinite_test ----

EXTENDS TLAPS, FiniteSets

THEOREM ASSUME NEW a,
               NEW b,
               IsFiniteSet(a)
        PROVE IsFiniteSet(a \ b)
    OBVIOUS

====
