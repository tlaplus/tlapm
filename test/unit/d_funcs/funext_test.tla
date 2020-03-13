---- MODULE funext_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW f \in [ A -> B ],
               NEW g \in [ A -> B ],
               \A x \in A : f[x] = g[x]
        PROVE f = g
    OBVIOUS

====
