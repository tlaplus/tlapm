---- MODULE append_test ----

EXTENDS TLAPS, Integers, Sequences

THEOREM ASSUME NEW S,
               NEW s \in Seq(S),
               NEW x \in S,
               NEW i \in Int
        PROVE /\ Append(s, x) \in Seq(S)
              /\ Len(Append(s, x)) = Len(s) + 1
              /\ (0 < i /\ i <= Len(s)) => Append(s, x)[i] = s[i]
              /\ Append(s, x)[Len(s) + 1] = x
    OBVIOUS

====
