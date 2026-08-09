---- MODULE strict_empty_target_test ----

(* Regression test for https://github.com/tlaplus/tlapm/issues/276

   An explicit target (`--line`) that selects no proof obligation otherwise
   reports "All 0 obligation proved" and exits 0, making an off-by-one line
   number look like a successful proof. Line 1 is the module header and selects
   no obligation. With `--strict` this is reported and tlapm exits with code 12
   (empty proof target).
*)

THEOREM TRUE OBVIOUS

====
command: ${TLAPM} --strict --nofp --line 1 ${FILE}
result: 12
stderr: No proof obligation found for the selected target
