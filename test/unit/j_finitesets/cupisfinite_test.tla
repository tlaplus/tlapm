---- MODULE cupisfinite_test ----

EXTENDS TLAPS, FiniteSets

THEOREM ASSUME NEW a,
               NEW b,
               IsFiniteSet(a),
               IsFiniteSet(b)
        PROVE IsFiniteSet(a \cup b)
    OBVIOUS

====
