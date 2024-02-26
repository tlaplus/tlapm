---- MODULE letchain_test ----

EXTENDS TLAPS

THEOREM ASSUME NEW a
        PROVE LET b == a
                  c == b
              IN
              a = c
    OBVIOUS

====
