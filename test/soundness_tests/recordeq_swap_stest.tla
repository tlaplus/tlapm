------------- MODULE recordeq_swap_stest --------------

\* Soundness control for `Encode.Rewrite.simpl_receq`.  Two record
\* constructors with equal domains but two field values transposed are
\* unequal in general, so the pass must pair fields by name, not by
\* position.  This obligation is invalid: SMT must report the negation
\* satisfiable (`sat`) and fail to prove it.  A soundness test passes iff
\* its obligation is not proved; were any backend to prove this, the
\* decomposition would be unsound.

EXTENDS TLAPS

THEOREM ASSUME NEW x,
               NEW y
        PROVE  [ foo |-> x, bar |-> y ] = [ foo |-> y, bar |-> x ]
BY SMT

=======================================================
