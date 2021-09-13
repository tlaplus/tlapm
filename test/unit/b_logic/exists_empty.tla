---- MODULE exists_empty_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW P
        PROVE (\E x \in {} : P) = FALSE
    OBVIOUS

====
