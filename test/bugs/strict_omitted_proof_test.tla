---- MODULE strict_omitted_proof_test ----

(* Regression test for https://github.com/tlaplus/tlapm/issues/271

   An explicit OMITTED proof also generates no obligation. With `--strict` the
   omission is reported as an error and tlapm exits with code 11 (incomplete
   proof).
*)

THEOREM TRUE
OMITTED

====
command: ${TLAPM} --strict --nofp ${FILE}
result: 11
stderr: Omitted proof at
stderr: Proof incomplete in module
