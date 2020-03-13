---- MODULE arrow_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW f
        PROVE f \in [ A -> B ] <=> /\ DOMAIN f = A
                                   /\ \A x \in A : f[x] \in B
    OBVIOUS

====
