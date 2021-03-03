---- MODULE hidedef_test ----

EXTENDS TLAPS

C == TRUE
HIDE DEF C

THEOREM C
    OBVIOUS

====
stderr: status:failed
