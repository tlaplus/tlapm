----------------------- MODULE quotient_remainder_stest ----------------------

\* The following used to be proved when
\* --debug disable_arithmetic was used.

EXTENDS Integers, TLAPS

LEMMA 7 % 0 \in 0 .. (0 - 1)
BY SMT

==============================================================================
flags: --debug disable_arithmetic
