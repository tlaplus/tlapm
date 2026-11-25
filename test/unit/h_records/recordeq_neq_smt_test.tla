---- MODULE recordeq_neq_smt_test ----

\* `Encode.Rewrite.simpl_receq` rewrites equalities (=) only; a disequality
\* (#) of two record constructors is not rewritten by the pass but follows
\* from the field-wise equality decomposition by negation: the records
\* differ iff some field differs.  Documents the expected SMT result.

EXTENDS TLAPS

THEOREM ASSUME NEW x, NEW y, NEW u, NEW v
        PROVE  ([ foo |-> x, bar |-> y ] # [ foo |-> u, bar |-> v ])
                    <=> (x # u \/ y # v)
BY SMT

====
