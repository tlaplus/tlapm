---- MODULE recorddom_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW x,
               NEW y,
               NEW u,
               NEW v
        PROVE [ foo |-> x, bar |-> y ] = [ foo |-> u, bar |-> v ]
                    <=> /\ x = u
                        /\ y = v
    OBVIOUS

====
