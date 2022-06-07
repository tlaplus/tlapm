---- MODULE setminuscard_test ----

EXTENDS TLAPS, FiniteSets, Integers

THEOREM ASSUME NEW a,
               NEW b,
               IsFiniteSet(a)
        PROVE Cardinality(a \ b) = Cardinality(a) - Cardinality(a \cap b)
    OBVIOUS

====
