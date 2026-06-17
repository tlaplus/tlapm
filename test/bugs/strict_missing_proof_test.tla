---- MODULE strict_missing_proof_test ----

(* Regression test for https://github.com/tlaplus/tlapm/issues/271

   A step whose proof is absent (here the bare QED step) generates no
   obligation, so without `--strict` the run reports "All 0 obligation proved"
   and exits 0, hiding the incomplete proof. With `--strict` the missing proof
   is reported as an error and tlapm exits with code 11 (incomplete proof).
*)

THEOREM TRUE
<1> QED

====
command: ${TLAPM} --strict --nofp ${FILE}
result: 11
stderr: Missing proof at
stderr: Proof incomplete in module
