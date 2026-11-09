------------- MODULE issue310_hash_collision_ptl_control_test --------------

\* The theorem is false: when y = TRUE, R63 is TRUE and R64 is FALSE.

EXTENDS TLAPS

VARIABLE y

R63 == y
R64 == ~y

THEOREM R63 => R64
BY PTL

===========================================================================
stderr: status:failed
stderr: prover:ls4
stderr: reason:false
nostderr: status:proved
nostderr: Unexpected error
nostderr: Unexpected exception
nostd*: ending abnormally
