---- MODULE tail_test ----

EXTENDS TLAPS, Integers, Sequences

THEOREM ASSUME NEW S,
               NEW s \in Seq(S),
               Len(s) > 0,
               NEW i \in Int
        PROVE /\ Tail(s) \in Seq(S)
              /\ Len(Tail(s)) = Len(s) - 1
              /\ (0 < i /\ i < Len(s)) => Tail(s)[i] = s[i + 1]
    OBVIOUS

====
