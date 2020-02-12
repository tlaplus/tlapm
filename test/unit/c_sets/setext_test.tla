---- MODULE setext_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a,
               \A x : x \notin a
        PROVE a = {}
    OBVIOUS

====
