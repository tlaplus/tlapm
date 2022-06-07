---- MODULE rectcard_test ----

EXTENDS TLAPS, FiniteSets, Integers

THEOREM ASSUME NEW a,
               NEW b,
               IsFiniteSet(a),
               IsFiniteSet(b)
        PROVE Cardinality([ foo : a, bar : b ]) = Cardinality(a) * Cardinality(b)
    OBVIOUS

====
