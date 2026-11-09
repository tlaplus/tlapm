------------- MODULE issue310_unused_context_test --------------

EXTENDS TLAPS

VARIABLE x

P == \E k : x = k

THEOREM ASSUME []P PROVE \A k : []P
BY SMT DEF P

=================================================================
stderr: status:proved
stderr: prover:smt
nostderr: status:failed
nostderr: Unexpected error
nostderr: Unexpected exception
nostd*: ending abnormally
