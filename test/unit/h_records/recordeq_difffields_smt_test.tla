---- MODULE recordeq_difffields_smt_test ----

\* Record constructors with unequal domains denote unequal records.
\* `Encode.Rewrite.simpl_receq` decomposes an equality only when both sides
\* have the same domain (its same_fieldset guard); otherwise it leaves the
\* equality for the solver, which refutes it by domain reasoning.  Here the
\* domains {"foo", "bar"} and {"foo"} differ, so the disequality holds.
\* `BY SMT` forces the pass.

EXTENDS TLAPS

THEOREM ASSUME NEW x,
               NEW y
        PROVE  [ foo |-> x, bar |-> y ] # [ foo |-> x ]
BY SMT

====
