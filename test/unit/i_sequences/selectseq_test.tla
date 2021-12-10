---- MODULE selectseq_test ----

EXTENDS TLAPS, Integers, Sequences

THEOREM ASSUME NEW S,
               NEW Test(_),
               NEW s \in Seq(S)
        PROVE /\ SelectSeq(s, Test) \in Seq(S),
              /\ Len(SelectSeq(s, Test)) <= Len(s)
              /\ \A i \in DOMAIN SelectSeq(s, Test) : Test(SelectSeq(s, Test)[i])
    OBVIOUS

====
