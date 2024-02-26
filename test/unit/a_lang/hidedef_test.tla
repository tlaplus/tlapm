---- MODULE hidedef_test ----

EXTENDS TLAPS

C == TRUE
HIDE DEF C

THEOREM TRUE
    BY C = C

====
