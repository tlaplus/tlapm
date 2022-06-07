---- MODULE singletoncard_test ----

EXTENDS TLAPS, FiniteSets, Integers

THEOREM ASSUME NEW a
        PROVE Cardinality({ a }) = 1
    OBVIOUS

====
