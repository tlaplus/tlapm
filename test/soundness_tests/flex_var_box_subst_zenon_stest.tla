--------------- MODULE flex_var_box_subst_zenon_stest ---------------

\* Zenon variant of flex_var_box_subst_smt_stest.
\* Current-state equality of flexible variables does not justify
\* substitution inside temporal formulas that depend on their behavior.

EXTENDS TLAPS

VARIABLES x, y

THEOREM x = y => ([](x = 0) => [](y = 0))
BY Zenon

=============================================================================
