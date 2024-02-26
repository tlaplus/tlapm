---- MODULE letsndord_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW H(_)
        PROVE LET G(F(_)) == TRUE IN
              G(H)
    OBVIOUS

====
