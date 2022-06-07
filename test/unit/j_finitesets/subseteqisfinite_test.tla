---- MODULE subseteqisfinite_test ----

EXTENDS TLAPS, FiniteSets

THEOREM ASSUME NEW a,
               NEW b,
               IsFiniteSet(b),
               a \subseteq b
        PROVE IsFiniteSet(a)
    OBVIOUS

====
