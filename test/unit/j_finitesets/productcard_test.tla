---- MODULE productcard_test ----

EXTENDS TLAPS, FiniteSets, Integers

THEOREM ASSUME NEW a,
               NEW b,
               IsFiniteSet(a),
               IsFiniteSet(b)
        PROVE Cardinality(a \X b) = Cardinality(a) * Cardinality(b)
    OBVIOUS

====
