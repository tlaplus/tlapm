------------- MODULE issue310_hash_collision_zenon_stest --------------

EXTENDS TLAPS

VARIABLE x

D33  == x
E280 == ~x

THEOREM []D33 => []E280
BY Zenon

=======================================================================
known: https://github.com/tlaplus/tlapm/issues/310
