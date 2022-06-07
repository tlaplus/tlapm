---- MODULE rangecard_test ----

EXTENDS TLAPS, FiniteSets, Integers

THEOREM ASSUME NEW a \in Int,
               NEW b \in Int
        PROVE /\ a <= b => Cardinality(a..b) = b - a + 1
              /\ a > b => Cardinality(a..b) = 0
    OBVIOUS

====
