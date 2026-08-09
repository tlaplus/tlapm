---- MODULE def_nondef_test ----

(* Regression test for https://github.com/tlaplus/tlapm/issues/280

   A DEF clause (`BY ... DEF X`, `USE DEF X`, or `HIDE DEF X`) that cites a
   name which is in scope but is not a definition -- a CONSTANT, a VARIABLE, or
   a NEW-declared constant/operator -- used to crash the whole run with
   `Failure("Proof.Gen.set_defn/doit")` ("Oops, this seems to be a bug in
   TLAPM"). It must instead be reported as a normal located error and the run
   must not abort abnormally.
*)

CONSTANT C
VARIABLE v

THEOREM TRUE BY DEF C

THEOREM TRUE
  <1>1. USE DEF v
  <1>2. QED OBVIOUS

THEOREM ASSUME NEW xx PROVE TRUE
  BY DEF xx

====
command: ${TLAPM} --nofp ${FILE}
result: 0
stderr: "C" is not a definition and cannot be used in a DEF clause
stderr: "v" is not a definition and cannot be used in a DEF clause
stderr: "xx" is not a definition and cannot be used in a DEF clause
nostderr: set_defn
nostderr: bug in TLAPM
nostderr: ending abnormally
