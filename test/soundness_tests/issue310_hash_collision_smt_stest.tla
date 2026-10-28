------------- MODULE issue310_hash_collision_smt_stest --------------

\* https://github.com/tlaplus/tlapm/issues/310
\* Abstracted terms are named "h" + the first five hex digits of the MD5
\* of their print, with no collision check.  md5("[]STATE_D33_") and
\* md5("[]STATE_E280_") both begin 4cb21, so []D33 and []E280 become the
\* same opaque constant.  The theorem is false: x = TRUE forever
\* satisfies []D33 but not []E280.

EXTENDS TLAPS

VARIABLE x

D33  == x
E280 == ~x

THEOREM []D33 => []E280
BY SMT

=====================================================================
known: https://github.com/tlaplus/tlapm/issues/310
