---- MODULE head_test ----

EXTENDS TLAPS, Integers, Sequences

THEOREM ASSUME NEW S,
               NEW s \in Seq(S)
        PROVE /\ Head(s) = s[1]
              /\ Len(s) > 0 => Head(s) \in S
    OBVIOUS

====
