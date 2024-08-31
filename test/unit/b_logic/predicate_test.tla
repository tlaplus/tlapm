---- MODULE predicate_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW P(_),
               NEW a
        PROVE P(a) => P(a)
    OBVIOUS

====
