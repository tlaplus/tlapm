---- MODULE recorddot_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW x,
               NEW y
        PROVE /\ [ foo |-> x, bar |-> y ].foo = x
              /\ [ foo |-> x, bar |-> y ].bar = y
    OBVIOUS

====
