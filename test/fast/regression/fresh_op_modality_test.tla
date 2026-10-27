------------- MODULE fresh_op_modality_test --------------

\* A declared operator under a modality is part of the abstracted term,
\* not a value argument.  These obligations are trivial once that term
\* reaches the solver.

EXTENDS TLAPS

CONSTANT P(_)
VARIABLE x

THEOREM <>(P(x)) => <>(P(x))
BY SMT

THEOREM ENABLED (P(x)) => ENABLED (P(x))
BY SMT

THEOREM ((P(x)) \cdot (x' = x)) => ((P(x)) \cdot (x' = x))
BY SMT

==========================================================
