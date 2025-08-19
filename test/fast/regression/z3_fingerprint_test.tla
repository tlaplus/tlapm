---- MODULE z3_fingerprint_test ----

EXTENDS TLAPS, Naturals

THEOREM foo == 2 + 2 = 4 BY Z3

====
command: ${TLAPM} --toolbox 0 0 ${FILE}
command: ${TLAPM} --toolbox 0 0 --noproving ${FILE}
stderr: already:true
