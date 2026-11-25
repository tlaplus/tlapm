----------------- MODULE flex_var_leadsto_subst_stest -----------------

\* TRUE ~> (x = 0) means that x = 0 infinitely often.
\* The theorem is false: x and y may agree initially while only x
\* reaches 0 infinitely often.

EXTENDS TLAPS

VARIABLES x, y

THEOREM x = y => ((TRUE ~> (x = 0)) => (TRUE ~> (y = 0)))
BY SMT

=============================================================================
