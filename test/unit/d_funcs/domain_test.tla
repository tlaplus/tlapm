---- MODULE domain_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW F(_)
        PROVE DOMAIN [ x \in A |-> F(x) ] = A
    OBVIOUS

====
