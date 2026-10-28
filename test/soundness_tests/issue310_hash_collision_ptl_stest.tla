------------- MODULE issue310_hash_collision_ptl_stest --------------

\* https://github.com/tlaplus/tlapm/issues/310
\* LS4 atoms are named like abstracted terms, by a 20-bit MD5 prefix of
\* their print.  md5("STATE_R63_") and md5("STATE_R699_") both begin
\* 0823c, so LS4 receives the single atom h0823c for R63 and R699.  The
\* theorem is false: it does not hold in a state with y = TRUE.

EXTENDS TLAPS

VARIABLE y

R63  == y
R699 == ~y

THEOREM R63 => R699
BY PTL

=====================================================================
known: https://github.com/tlaplus/tlapm/issues/310
