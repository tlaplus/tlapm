---- MODULE recordeq_fieldorder_smt_test ----

\* A record constructor denotes a function whose domain is a set of fields,
\* so the order in which fields are written is immaterial:
\* [ foo |-> x, bar |-> y ] and [ bar |-> y, foo |-> x ] denote the same
\* record.  `Encode.Rewrite.simpl_receq` pairs fields by name, hence the
\* equality decomposes to x = x /\ y = y and holds.  `BY SMT` forces the pass.

EXTENDS TLAPS

THEOREM ASSUME NEW x,
               NEW y
        PROVE  [ foo |-> x, bar |-> y ] = [ bar |-> y, foo |-> x ]
BY SMT

====
