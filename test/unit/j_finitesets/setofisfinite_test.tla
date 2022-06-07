---- MODULE setofisfinite_test ----

EXTENDS TLAPS, FiniteSets

THEOREM ASSUME NEW F(_),
               NEW a,
               IsFiniteSet(a)
        PROVE IsFiniteSet({ F(x) : x \in a })
    OBVIOUS

====
