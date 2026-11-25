---- MODULE smt_rlimit_bad_test ----

(* Regression test for https://github.com/tlaplus/tlapm/issues/281

   A malformed SMT budget string must be rejected with a normal located error
   rather than being silently accepted or crashing.
*)

EXTENDS TLAPS, Naturals

THEOREM 2 + 2 = 4 BY SMTT("bad")

====
command: ${TLAPM} --nofp ${FILE}
result: 3
stderr: Invalid SMT budget
nostderr: bug in TLAPM
