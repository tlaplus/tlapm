---- MODULE nary_fcnappi_test ----
EXTENDS TLAPS


f == [x \in {TRUE} \X {TRUE} |-> TRUE]

THEOREM f[TRUE, TRUE] = TRUE
<1>1. <<TRUE, TRUE>> \in {TRUE} \X {TRUE}
    OBVIOUS
<1> QED
    BY <1>1, SMT DEF f

============================
