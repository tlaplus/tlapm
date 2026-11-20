------------- MODULE prime_stale_depth_stest --------------

\* False. y' = y' is visited first and records a scope boundary.
\* The later prime on <<a>> is already inside the LAMBDA, so
\* substituting x for a makes the right conjunct <<x'>> = <<x>>.
\* If that boundary is left in place, a is treated as bound by the
\* earlier push, the prime is dropped, and both sides are <<x>>.

EXTENDS TLAPS

VARIABLES x, y

H(F(_)) == F(x)

THEOREM (y' = y') /\ (H(LAMBDA a : <<a>>') = H(LAMBDA a : <<a>>))
BY Isa

============================================================
\* related: prime_tuple_inside_lambda_stest
