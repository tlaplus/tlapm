---- MODULE cvc3_false_test ----

EXTENDS TLAPS

THEOREM t == FALSE BY CVC3T(35)

====
stderr: status:failed
