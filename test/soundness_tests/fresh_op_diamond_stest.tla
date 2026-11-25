---------------- MODULE fresh_op_diamond_stest -----------------

\* The theorem is false: P may hold of x when Q does not, so eventual
\* P(x) does not imply eventual Q(x).

EXTENDS TLAPS

CONSTANT P(_)
CONSTANT Q(_)
VARIABLE x

THEOREM <>(P(x)) => <>(Q(x))
BY SMT

=============================================================
