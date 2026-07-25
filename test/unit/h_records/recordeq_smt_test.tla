---- MODULE recordeq_smt_test ----

\* A record is a function whose domain is its set of fields; two records are
\* equal iff they have equal domains and agree on every field.  The SMT
\* encoding pass `Encode.Rewrite.simpl_receq` rewrites an equality of two
\* record constructors with equal domains into the conjunction of the
\* field-wise equalities before encoding, so the solver need not appeal to
\* function/record extensionality.  `recordext_test` states the same
\* equivalence under the default backend; `BY SMT` here forces the pass.

EXTENDS TLAPS

THEOREM ASSUME NEW x,
               NEW y,
               NEW u,
               NEW v
        PROVE  [ foo |-> x, bar |-> y ] = [ foo |-> u, bar |-> v ]
                    <=> /\ x = u
                        /\ y = v
BY SMT

====
