---- MODULE predarg_test ----

(* NOTE: Requires higher-order unification *)

EXTENDS TLAPS

F(P(_), x) == P(x)

THEOREM DefF ==
        ASSUME NEW P(_),
               NEW x,
               P(x)
        PROVE F(P, x)
    (*BY DEF F*)

THEOREM ASSUME NEW x
        PROVE F(LAMBDA y : y = y, x)
    BY DefF

====
