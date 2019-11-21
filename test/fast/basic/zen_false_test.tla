---- MODULE zen_false_test ----

EXTENDS TLAPS

THEOREM t == FALSE BY ZenonT (5)

====
stderr: status:failed
