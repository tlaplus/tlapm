---- MODULE subseq_test ----

EXTENDS TLAPS, Integers, Sequences

THEOREM ASSUME NEW S,
               NEW s \in Seq(S),
               NEW i \in Int,
               NEW j \in Int,
               0 < i,
               i <= j,
               NEW k \in Int
        PROVE /\ SubSeq(s, i, j) \in Seq(S)
              /\ Len(SubSeq(s, i, j)) = j - i + 1
              /\ (0 < k /\ k <= j - i + 1) => SubSeq(s, i, j)[k] = s[i + k - 1]
    OBVIOUS

====
