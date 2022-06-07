---- MODULE cupcard_test ----

EXTENDS TLAPS, FiniteSets, Integers

THEOREM ASSUME NEW a,
               NEW b,
               IsFiniteSet(a),
               IsFiniteSet(b)
        PROVE Cardinality(a \cup b) = Cardinality(a) + Cardinality(b) - Cardinality(a \cap b)
    OBVIOUS

====
