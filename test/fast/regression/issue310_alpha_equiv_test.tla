------------- MODULE issue310_alpha_equiv_test --------------

\* https://github.com/tlaplus/tlapm/issues/310
\* Abstracted terms that differ only in the names of their bound
\* variables are the same term and must get the same name.  Naming them
\* by a hash of their print gives them different names, so this valid
\* theorem fails.

VARIABLE w

THEOREM [](\E k : w = k) => [](\E j : w = j)
OBVIOUS

=============================================================
