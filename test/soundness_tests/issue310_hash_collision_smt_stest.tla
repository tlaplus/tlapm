------------- MODULE issue310_hash_collision_smt_stest --------------

\* The theorem is false: x = TRUE forever satisfies []D33, while
\* []E280 requires x to be FALSE forever.

EXTENDS TLAPS

VARIABLE x

D33  == x
E280 == ~x

THEOREM []D33 => []E280
BY SMT

=====================================================================
known: https://github.com/tlaplus/tlapm/issues/310
