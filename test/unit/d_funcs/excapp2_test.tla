---- MODULE excapp_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW f \in [ A -> B ],
               NEW x \in A,
               NEW a,
               NEW y \in A,
               y # x
        PROVE LET g == [ f EXCEPT ![x] = a ] IN
              g[y] = f[y]
    OBVIOUS

====
