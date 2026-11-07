---------------- MODULE fresh_op_diamond_stest -----------------

\* The theorem is false: P may hold of x when Q does not, so eventual
\* P(x) does not imply eventual Q(x).  P and Q are positive-arity
\* operators and must not be passed to the solver as values.

EXTENDS TLAPS

CONSTANT P(_)
CONSTANT Q(_)
VARIABLE x

THEOREM <>(P(x)) => <>(Q(x))
BY SMT

=============================================================
