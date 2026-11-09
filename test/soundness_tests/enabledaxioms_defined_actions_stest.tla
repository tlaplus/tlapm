------------- MODULE enabledaxioms_defined_actions_stest --------------

\* A is x' = 1 and B is x' = 2, so A /\ B requires x' to be both 1 and
\* 2.  ENABLED (A /\ B) is false.

EXTENDS TLAPS

VARIABLE x

A == x' = 1
B == x' = 2

THEOREM ENABLED (A /\ B)
<1>1. A \in BOOLEAN
    BY DEF A
<1>2. B \in BOOLEAN
    BY DEF B
<1>3. (ENABLED A) /\ (ENABLED B)
    BY ExpandENABLED, AutoUSE
<1> QED
    BY <1>1, <1>2, <1>3, ENABLEDaxioms

============================================================
known: https://github.com/tlaplus/tlapm/issues/new
