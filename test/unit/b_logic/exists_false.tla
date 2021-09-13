---- MODULE exists_false_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW S
        PROVE (\E x \in S : FALSE) = FALSE
    OBVIOUS

====
