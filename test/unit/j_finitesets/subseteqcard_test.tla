---- MODULE subseteqcard_test ----

EXTENDS TLAPS, FiniteSets, Integers

THEOREM ASSUME NEW a,
               NEW b,
               IsFiniteSet(b),
               a \subseteq b
        PROVE /\ Cardinality(a) <= Cardinality(b)
              /\ Cardinality(a) = Cardinality(b) => a = b
    OBVIOUS

====
