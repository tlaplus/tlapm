---- MODULE recordeq_if_smt_test ----

\* `Encode.Rewrite.simpl_receq` decomposes an equality only when both sides
\* are record constructors; a field value is copied verbatim into the
\* corresponding field equality.  In particular it must not distribute `=`
\* over IF-THEN-ELSE: that is unsound in TLA+, where the guard is not assumed
\* Boolean and IF-THEN-ELSE with a non-Boolean guard denotes an unspecified
\* value.  Here field `foo` is identical on both sides and field `bar`
\* reduces to the assumption x = z.

EXTENDS TLAPS

THEOREM ASSUME NEW c,
               NEW x,
               NEW y,
               NEW z,
               x = z
        PROVE  [ foo |-> (IF c THEN x ELSE y), bar |-> x ]
                    = [ foo |-> (IF c THEN x ELSE y), bar |-> z ]
BY SMT

====
