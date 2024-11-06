---- MODULE unary_fcnapp_test ----
EXTENDS TLAPS


f == [x \in {TRUE} |-> TRUE]

THEOREM f[TRUE] = TRUE
BY SMT DEF f

============================
