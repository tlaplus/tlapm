---- MODULE FingerprintVariablesParameters_test ----
(* Test to ensure there is no coincidence between
how variables and bound constants are fingerprinted.

When this was a bug, the first run of TLAPM
did not prove the second theorem below,
but the assertions of the two theorems had identical
fingerprints, so the second run of TLAPM proved
both theorems. The commands for the test harness
check this, by running TLAPM twice.
*)

VARIABLE x

THEOREM \E y:  y # x
OBVIOUS

THEOREM \E y:  y # y
OBVIOUS

====================================
command: ${TLAPM} --toolbox 0 0 ${FILE}
stderr: 1/2 obligations failed
command: ${TLAPM} --toolbox 0 0 ${FILE}
stderr: 1/2 obligations failed
