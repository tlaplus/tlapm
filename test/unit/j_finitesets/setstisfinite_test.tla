---- MODULE setstisfinite_test ----

EXTENDS TLAPS, FiniteSets

THEOREM ASSUME NEW P(_),
               NEW a,
               IsFiniteSet(a)
        PROVE IsFiniteSet({ x \in a : P(x) })
    OBVIOUS

====
