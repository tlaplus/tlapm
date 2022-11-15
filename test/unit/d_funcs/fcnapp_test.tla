---- MODULE fcnapp_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW F(_),
               NEW z
        PROVE z \in A => [ x \in A |-> F(x) ][z] = F(z)
    OBVIOUS

====
