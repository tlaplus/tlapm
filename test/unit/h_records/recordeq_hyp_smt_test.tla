---- MODULE recordeq_hyp_smt_test ----

\* `Encode.Rewrite.simpl_receq` rewrites record-constructor equalities
\* wherever they occur, including among the assumptions of an ASSUME/PROVE.
\* From an assumed equality of two record constructors with equal domains,
\* each field equality follows.  `BY SMT` forces the pass.

EXTENDS TLAPS

THEOREM ASSUME NEW x, NEW y, NEW u, NEW v,
               [ foo |-> x, bar |-> y ] = [ foo |-> u, bar |-> v ]
        PROVE  /\ x = u
               /\ y = v
BY SMT

====
