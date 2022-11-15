---- MODULE unary_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW F(_),
               NEW a
               PROVE F(a) = F(a)
    OBVIOUS

====
