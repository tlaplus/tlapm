---- MODULE z3_false_test ----

EXTENDS TLAPS

THEOREM t == FALSE BY Z3

====
stderr: reason:false
