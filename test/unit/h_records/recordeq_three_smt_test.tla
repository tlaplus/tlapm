---- MODULE recordeq_three_smt_test ----

\* Field-wise decomposition of an equality of two three-field record
\* constructors, exercising the n-ary conjunction of field equalities built
\* by `Encode.Rewrite.simpl_receq` for domains of size greater than two.
\* `BY SMT` forces the pass.

EXTENDS TLAPS

THEOREM ASSUME NEW x, NEW y, NEW z,
               NEW p, NEW q, NEW r
        PROVE  ([ a |-> x, b |-> y, c |-> z ] = [ a |-> p, b |-> q, c |-> r ])
                    <=> /\ x = p
                        /\ y = q
                        /\ z = r
BY SMT

====
