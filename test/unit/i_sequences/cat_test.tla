---- MODULE cat_test ----

EXTENDS TLAPS, Integers, Sequences

THEOREM ASSUME NEW S,
               NEW s \in Seq(S),
               NEW t \in Seq(S),
               NEW i \in Int
        PROVE /\ s \o t \in Seq(S)
              /\ Len(s \o t) = Len(s) + Len(t)
              /\ (0 < i /\ i <= Len(s)) => (s \o t)[i] = s[i]
              /\ (Len(s) < i /\ i <= Len(s) + Len(t)) => (s \o t)[i] = t[i - Len(s)]
    OBVIOUS

====
