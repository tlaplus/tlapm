---- MODULE sndordthm_test ----

EXTENDS TLAPS

THEOREM Thm ==
        ASSUME NEW F(_),
               NEW a
        PROVE F(a)

THEOREM ASSUME NEW F(_),
               NEW a
        PROVE a
    BY Thm

====
