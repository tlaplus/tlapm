------------- MODULE ambiguous_precedence_test --------------

\* https://github.com/tlaplus/rfcs/issues/28
\* Intended (TRUE)
\* {} \notin ((SUBSET {}) \cap {})
\* Legacy (FALSE)
\* {} \notin (SUBSET ({} \cap {}))

THEOREM
  ASSUME {} \notin SUBSET {} \cap {}
  PROVE FALSE
OBVIOUS

=============================================================
result: 3
stderr: ambiguous expression: operators SUBSET and \\cap have conflicting precedence; use parentheses
nostderr: @!!status:proved
