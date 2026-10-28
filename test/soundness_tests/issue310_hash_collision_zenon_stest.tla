------------- MODULE issue310_hash_collision_zenon_stest --------------

\* https://github.com/tlaplus/tlapm/issues/310
\* Zenon variant of issue310_hash_collision_smt_stest: the colliding name
\* is produced by the shared front end, not by the SMT encoding.

EXTENDS TLAPS

VARIABLE x

D33  == x
E280 == ~x

THEOREM []D33 => []E280
BY Zenon

=======================================================================
known: https://github.com/tlaplus/tlapm/issues/310
