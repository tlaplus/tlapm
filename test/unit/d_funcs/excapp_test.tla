---- MODULE excapp_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW A,
               NEW B,
               NEW f \in [ A -> B ],
               NEW x \in A,
               NEW a
        PROVE LET g == [ f EXCEPT ![x] = a ] IN
              \A z \in A :
                    g[z] =
                        IF z = x THEN a
                        ELSE f[z]
    OBVIOUS

====
