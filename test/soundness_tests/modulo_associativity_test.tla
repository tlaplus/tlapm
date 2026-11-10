------------- MODULE modulo_associativity_test --------------
EXTENDS Naturals

\* https://github.com/tlaplus/rfcs/issues/28
\* Intended (TRUE)
\* 5 % (4 % 3) = 0
\* Legacy (FALSE)
\* (5 % 4) % 3 = 0

THEOREM
  ASSUME 5 % 4 % 3 = 0
  PROVE FALSE
OBVIOUS

=============================================================
result: 3
stderr: ambiguous expression: operators % and % have conflicting precedence; use parentheses
nostderr: @!!status:proved
