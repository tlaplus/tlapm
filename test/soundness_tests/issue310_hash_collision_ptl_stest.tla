------------- MODULE issue310_hash_collision_ptl_stest --------------

EXTENDS TLAPS

VARIABLE y

R63  == y
R699 == ~y

THEOREM R63 => R699
BY PTL

=====================================================================
known: https://github.com/tlaplus/tlapm/issues/310
