---- MODULE selectseq_test ----

EXTENDS TLAPS, Integers, Sequences

THEOREM ASSUME NEW S,
               NEW Test(_),
               NEW s \in Seq(S),
               NEW x
        PROVE /\ SelectSeq(s, Test) \in Seq(S)
              /\ Len(SelectSeq(s, Test)) <= Len(s)
              /\ Test(x) => SelectSeq(Append(s, x), Test) = Append(SelectSeq(s, Test), x)
              /\ ~ Test(x) => SelectSeq(Append(s, x), Test) = SelectSeq(s, Test)
              /\ \A i \in DOMAIN SelectSeq(s, Test) : Test(SelectSeq(s, Test)[i])
    OBVIOUS

====
