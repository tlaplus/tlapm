---- MODULE rectsort_test ----

EXTENDS TLAPS

\* If record fields are sorted during preprocessing, this proof is easy.
\* Otherwise, backends may get stuck because the expression [ bar : _, foo : _ ]
\* is needed but absent.
THEOREM ASSUME NEW S, NEW T,
               NEW r,
               r.foo \in S,
               r.bar \in T
        PROVE [ bar |-> r.bar, foo |-> r.foo ] \in [ foo : S, bar : T ]
    OBVIOUS

====
