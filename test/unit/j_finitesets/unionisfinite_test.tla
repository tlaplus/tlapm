---- MODULE unionisfinite_test ----

EXTENDS TLAPS, FiniteSets

THEOREM ASSUME NEW a,
               IsFiniteSet(a),
               \A x : x \in a => IsFiniteSet(x)
        PROVE IsFiniteSet(UNION a)
    OBVIOUS

====
