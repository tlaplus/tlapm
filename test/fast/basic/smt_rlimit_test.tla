---- MODULE smt_rlimit_test ----

(* Regression test for https://github.com/tlaplus/tlapm/issues/281

   `SMTT`/`Z3T` accept a string budget of the form "rN" that bounds the
   underlying Z3 solver by a deterministic `rlimit` budget (a multiple of a
   fixed base resource count) instead of a wall-clock timeout. A generous
   budget must discharge these obligations just like the ordinary
   numeric-timeout form.
*)

EXTENDS TLAPS, Naturals

THEOREM t1 == 2 + 2 = 4 BY SMTT("r10")

THEOREM t2 == 2 * 3 = 6 BY Z3T("r10")

====
