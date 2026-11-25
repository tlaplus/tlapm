------------------- MODULE flex_var_cdot_subst_stest -------------------

\* The theorem is false because x = y does not imply x' = y'.

EXTENDS TLAPS

VARIABLES x, y

THEOREM x = y => (((x = 0) \cdot (x' = 1)) => ((y = 0) \cdot (y' = 1)))
BY SMT

=============================================================================
