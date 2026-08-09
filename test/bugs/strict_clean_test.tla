---- MODULE strict_clean_test ----

(* Regression test for the `--strict` option (issues 271 and 276): a complete
   proof with all obligations discharged must still exit 0 under `--strict`,
   i.e. the strict checks must not introduce false positives.
*)

THEOREM TRUE OBVIOUS

====
command: ${TLAPM} --strict --nofp ${FILE}
result: 0
nostderr: Proof incomplete
nostderr: No proof obligation found
