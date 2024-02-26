---- MODULE letfunction_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a
        PROVE LET F(x) == TRUE IN
              F(a)
    OBVIOUS

====
