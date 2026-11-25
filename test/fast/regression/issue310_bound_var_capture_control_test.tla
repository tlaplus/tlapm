------------- MODULE issue310_bound_var_capture_control_test --------------

\* The theorem is false: with c = 2 and w = <<1, 2>> forever,
\* [](Q(c)) holds and [](P(c, c)) does not.

EXTENDS TLAPS

VARIABLE w

P(z, u) == \E k : w = <<z, u>>
Q(u)    == \E k : w = <<k, u>>

THEOREM ASSUME NEW c PROVE [](Q(c)) => [](P(c, c))
BY SMT DEF P, Q

===========================================================================
stderr: status:failed
stderr: prover:smt
stderr: SMT failed with status = sat
nostderr: status:proved
nostderr: Unexpected error
nostderr: Unexpected exception
nostd*: ending abnormally
