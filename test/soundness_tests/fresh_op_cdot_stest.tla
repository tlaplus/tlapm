----------------- MODULE fresh_op_cdot_stest ------------------

\* The theorem is false: x can be 0 now and 1 next while P(x) = 0
\* and Q(x) # 0.  The two compositions are then not equivalent.

EXTENDS TLAPS

CONSTANT P(_)
CONSTANT Q(_)
VARIABLE x

THEOREM ((P(x) = 0) \cdot (x' = 1)) => ((Q(x) = 0) \cdot (x' = 1))
BY SMT

================================================================
