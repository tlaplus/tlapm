---------------- MODULE flex_var_box_subst_isa_stest ----------------

\* The theorem is false: x and y may initially both be 0, after which
\* x stays 0 while y changes.

EXTENDS TLAPS

VARIABLES x, y

THEOREM x = y => ([](x = 0) => [](y = 0))
BY Isa

=============================================================================
