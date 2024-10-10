---- MODULE fingerprint_13_12_07_test ----

EXTENDS TLAPS

CONSTANT S

THEOREM ASSUME NEW x \in S
PROVE S # {}
OBVIOUS

THEOREM S # {} OBVIOUS

====
command: ${TLAPM} --toolbox 0,0 --threads 1 --cleanfp ${FILE}
stderr: status:failed
