---- MODULE len_test ----

EXTENDS TLAPS, Integers, Sequences

THEOREM ASSUME NEW S,
               NEW s \in Seq(S)
        PROVE /\ Len(s) \in Nat
              /\ DOMAIN s = 1..Len(s)
    OBVIOUS

====
