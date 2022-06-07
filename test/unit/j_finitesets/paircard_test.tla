---- MODULE paircard_test ----

EXTENDS TLAPS, FiniteSets, Integers

THEOREM ASSUME NEW a,
               NEW b,
               a # b
        PROVE Cardinality({ a, b }) = 2
    OBVIOUS

====
