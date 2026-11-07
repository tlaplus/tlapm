----------------- MODULE flex_var_box_subst_smt_stest -----------------

\* Equality of flexible variables in the current state does not imply
\* equivalence of temporal formulas about their future values.
\* The theorem is false: x and y may initially both be 0, after which
\* x stays 0 while y changes. This test guards against abstractions
\* that allow substituting x for y inside [] using current-state equality.

EXTENDS TLAPS

VARIABLES x, y

THEOREM x = y => ([](x = 0) => [](y = 0))
BY SMT

=============================================================================
