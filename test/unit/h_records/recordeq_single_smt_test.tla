---- MODULE recordeq_single_smt_test ----

\* Field-wise decomposition of an equality of two single-field record
\* constructors by `Encode.Rewrite.simpl_receq`.  `BY SMT` forces the pass.

EXTENDS TLAPS

THEOREM ASSUME NEW x,
               NEW y
        PROVE  ([ foo |-> x ] = [ foo |-> y ]) <=> (x = y)
BY SMT

====
