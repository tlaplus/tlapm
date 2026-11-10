------------- MODULE operator_valued_expr_smt_test --------------

\* The theorem is valid: P(x) holds now, so it holds eventually.
\* Coalescing <>P(x) passes the operator P as a dependency argument.
\* SMT type synthesis does not support that operator-valued expression;
\* report the limitation as a failed obligation without an exception backtrace.

EXTENDS TLAPS

VARIABLE x

THEOREM ASSUME NEW P(_), P(x) PROVE <>P(x)
BY SMT

===============================================================
stderr: status:failed
stderr: prover:smt
stderr: reason:Type.Synthesize: Operator-valued expression is not supported here
nostderr: status:proved
nostd*: Unexpected error
nostd*: Unexpected exception
nostd*: Invalid_type_downcast
nostd*: ending abnormally
