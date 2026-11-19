----------------------- MODULE prime_nested_inner_test -----------------------

\* N stays unexpanded, so the action frontend distributes the prime
\* while the binders are present. The prime sits on the inner
\* application. The outer parameter is already in scope; the inner
\* parameter is bound while the prime is pushed under it.

EXTENDS Naturals, TLAPS

VARIABLE y

N(F(_)) == F(0)

THEOREM N(LAMBDA a : N(LAMBDA b : <<a, b, y>>) ')
      = N(LAMBDA a : N(LAMBDA b : <<a', b, y'>>))
BY Isa

=============================================================================
known: https://github.com/tlaplus/tlapm/issues/newCompletenessIssue
