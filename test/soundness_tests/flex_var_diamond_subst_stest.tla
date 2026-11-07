----------------- MODULE flex_var_diamond_subst_stest -----------------

\* Eventualities depend on future behavior, not just current-state values.
\* The theorem is false: x and y may initially agree, after which x
\* reaches 0 while y never does. This test guards against abstractions
\* that allow substituting x for y inside <> using current-state equality.

EXTENDS TLAPS

VARIABLES x, y

THEOREM x = y => (<>(x = 0) => <>(y = 0))
BY SMT

=============================================================================
