---- MODULE seq_test ----

EXTENDS TLAPS, Integers, Sequences

THEOREM ASSUME NEW S,
               NEW D,
               NEW F(_)
        PROVE LET s == [ i \in D |-> F(i) ] IN
              s \in Seq(S) <=>
                /\ Len(s) \in Nat
                /\ D = 1..Len(s)
                /\ \A i \in D : F(i) \in S
    OBVIOUS

====
