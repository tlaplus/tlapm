---- MODULE sequences_test ----

EXTENDS TLAPS, Sequences

(* NOTE Sequences are supported to the extent that the operators
    are declared in the result problem. No axioms for sequences
    are provided.
*)

Triv(x) == x = x

THEOREM ASSUME NEW S,
               NEW s,
               NEW t,
               NEW e,
               NEW m,
               NEW n,
               NEW Test(_),
               Triv(Seq(S)),
               Triv(Len(s)),
               Triv(s \o t),
               Triv(Append(s, e)),
               Triv(Head(s)),
               Triv(Tail(s)),
               Triv(SubSeq(s, m, n)),
               Triv(SelectSeq(s, Test))
        PROVE TRUE
    BY DEF Triv

====
