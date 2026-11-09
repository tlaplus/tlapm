------------- MODULE issue310_hash_collision_ptl_control_test --------------

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
