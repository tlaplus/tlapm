----------------------- MODULE quotient_remainder_stest ----------------------

\* The following used to be proved when
\* --debug disable_arithmetic was used.

EXTENDS Integers, TLAPS

LEMMA (0 - 7) \div 2 \in Nat
BY SMT

==============================================================================
flags: --debug disable_arithmetic
