------------- MODULE prime_tuple_inner_vs_free_stest --------------

\* False. The left side is <<x', y'>> and the right side is <<x, y'>>.
\* The prime on the tuple must prime a as well as the free variable y.

EXTENDS TLAPS

VARIABLES x, y

H(F(_)) == F(x)

THEOREM H(LAMBDA a : <<a, y>>') = H(LAMBDA a : <<a, y'>>)
BY Isa

============================================================
\* related: prime_tuple_inside_lambda_stest
