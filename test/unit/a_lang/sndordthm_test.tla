---- MODULE sndordthm_test ----

(* NOTE: Requires higher-order unification *)

EXTENDS TLAPS

THEOREM Thm ==
        ASSUME NEW F(_),
               NEW a
        PROVE F(a)

THEOREM ASSUME NEW F(_),
               NEW a
        PROVE F(a)
    BY Thm

====
