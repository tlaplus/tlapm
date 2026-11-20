----------------------- MODULE prime_nested_outer_test -----------------------

\* N stays unexpanded, so the action frontend distributes the prime
\* while the binders are present. An outer prime is pushed under both
\* LAMBDAs. The inner one is an operator argument, which is where
\* TLA+ allows a LAMBDA. The free state variable is primed.

EXTENDS Naturals, TLAPS

VARIABLE y

N(F(_)) == F(0)

THEOREM N(LAMBDA a : N(LAMBDA b : <<a, b, y>>))'
      = N(LAMBDA a : N(LAMBDA b : <<a, b, y'>>))
BY Isa

=============================================================================
