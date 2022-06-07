---- MODULE capcard_test ----

EXTENDS TLAPS, FiniteSets, Integers

THEOREM ASSUME NEW a,
               NEW b,
               IsFiniteSet(a)
        PROVE /\ Cardinality(a \cap b) = Cardinality(b \cap a)
              /\ Cardinality(a \cap b) = Cardinality(a) - Cardinality(a \ b)
    OBVIOUS

====
