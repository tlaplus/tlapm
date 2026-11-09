------------- MODULE issue310_hash_collision_control_test --------------

EXTENDS TLAPS

VARIABLE x

D33 == x
D34 == ~x

THEOREM []D33 => []D34
BY SMT

=======================================================================
stderr: status:failed
stderr: prover:smt
stderr: SMT failed with status = sat
nostderr: status:proved
nostderr: Unexpected error
nostderr: Unexpected exception
nostd*: ending abnormally
