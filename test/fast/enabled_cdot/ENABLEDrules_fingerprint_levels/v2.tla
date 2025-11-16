---- MODULE temp ----
EXTENDS TLAPS


VARIABLE x


THEOREM
    ASSUME x' = 1
    PROVE ENABLED (x' = 1) => ENABLED (x' = 1 \/ x' = 2)
<1>1. (x' = 1) => (x' = 1 \/ x' = 2)
    OBVIOUS
<1> QED
    BY ONLY <1>1, ENABLEDrules


=====================================================
