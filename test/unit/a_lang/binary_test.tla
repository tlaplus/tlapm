---- MODULE binary_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW F(_, _),
               NEW a,
               NEW b
               PROVE F(a, b) = F(a, b)
    OBVIOUS

====
