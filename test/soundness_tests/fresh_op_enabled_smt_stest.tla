-------------- MODULE fresh_op_enabled_smt_stest ---------------

\* The theorem is false.  ENABLED (P(x)) holds exactly when P(x) does,
\* and P(x) does not imply Q(x).

EXTENDS TLAPS

CONSTANT P(_)
CONSTANT Q(_)
VARIABLE x

THEOREM ENABLED (P(x)) => ENABLED (Q(x))
BY SMT

===============================================================
