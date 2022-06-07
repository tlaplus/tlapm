---- MODULE rectisfinite_test ----

EXTENDS TLAPS, FiniteSets

THEOREM ASSUME NEW a,
               NEW b,
               IsFiniteSet(a),
               IsFiniteSet(b)
        PROVE IsFiniteSet([ foo : a, bar : b ])
    OBVIOUS

====
