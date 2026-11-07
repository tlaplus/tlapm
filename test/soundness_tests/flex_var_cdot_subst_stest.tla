------------------- MODULE flex_var_cdot_subst_stest -------------------

\* (x = 0) \cdot (x' = 1) holds when x is 0 now and 1 in the next state.
\* The theorem is false because x = y does not imply x' = y'.
\* This test guards against abstractions that make the two compositions
\* interchangeable based solely on current-state equality.

EXTENDS TLAPS

VARIABLES x, y

THEOREM x = y => (((x = 0) \cdot (x' = 1)) => ((y = 0) \cdot (y' = 1)))
BY SMT

=============================================================================
