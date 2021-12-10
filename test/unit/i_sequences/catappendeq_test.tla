---- MODULE catappendeq_test ----

EXTENDS TLAPS, Integers, Sequences

THEOREM ASSUME NEW S,
               NEW s \in Seq(S),
               NEW x \in S
        PROVE Append(s, x) = s \o << x >>
    OBVIOUS

====
