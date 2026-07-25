---- MODULE recordeq_nested_smt_test ----

\* `Encode.Rewrite.simpl_receq` recurses into nested record constructors: an
\* equality of records whose field values are themselves record constructors
\* reduces to the conjunction of the equalities of the innermost fields.
\* `BY SMT` forces the pass.

EXTENDS TLAPS

THEOREM ASSUME NEW x, NEW y, NEW z,
               NEW u, NEW v, NEW w
        PROVE  ([ a |-> [ p |-> x, q |-> y ], b |-> z ]
                    = [ a |-> [ p |-> u, q |-> v ], b |-> w ])
                    <=> /\ x = u
                        /\ y = v
                        /\ z = w
BY SMT

====
