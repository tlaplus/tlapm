---- MODULE props_test ----

EXTENDS TLAPS

THEOREM FALSE => (TRUE /\ (TRUE \/ FALSE))
    OBVIOUS

====
