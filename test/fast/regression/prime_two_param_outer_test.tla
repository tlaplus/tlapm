--------------------- MODULE prime_two_param_outer_test ---------------------

\* G stays unexpanded, so the action frontend distributes the prime
\* while the binder is present. Both parameters are bound while an
\* outer prime is pushed under the LAMBDA. The free state variable
\* is primed.

EXTENDS Naturals, TLAPS

VARIABLE x

G(F(_,_)) == F(0, 1)

THEOREM G(LAMBDA a, b : <<a, b, x>>)'
      = G(LAMBDA a, b : <<a, b, x'>>)
BY Isa

=============================================================================
