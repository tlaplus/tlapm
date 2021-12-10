---- MODULE empty_test ----

EXTENDS TLAPS, Integers, Sequences

THEOREM ASSUME NEW S
        PROVE /\ << >> \in Seq(S)
              /\ Len(<< >>) = 0
    OBVIOUS

====
