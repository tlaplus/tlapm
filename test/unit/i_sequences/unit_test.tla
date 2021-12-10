---- MODULE unit_test ----

EXTENDS TLAPS, Integers, Sequences

THEOREM ASSUME NEW S,
               NEW x \in S
        PROVE /\ << x >> \in Seq(S)
              /\ Len(<< x >>) = 1
    OBVIOUS

====
