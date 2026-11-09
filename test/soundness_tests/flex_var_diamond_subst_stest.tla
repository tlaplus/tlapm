----------------- MODULE flex_var_diamond_subst_stest -----------------

\* The theorem is false: x and y may initially agree, after which x
\* reaches 0 while y never does.

EXTENDS TLAPS

VARIABLES x, y

THEOREM x = y => (<>(x = 0) => <>(y = 0))
BY SMT

=============================================================================
