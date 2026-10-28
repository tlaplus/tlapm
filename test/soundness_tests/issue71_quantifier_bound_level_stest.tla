------------- MODULE issue71_quantifier_bound_level_stest --------------

\* https://github.com/tlaplus/tlapm/issues/71
\* The level of \E x \in t : x = x ignores the variable t in the bound,
\* so X is taken to be constant and X' is identified with X.  The theorem
\* is false: it fails for a step from t = {} to t = {1}.

EXTENDS TLAPS

VARIABLE t

X == \E x \in t : x = x

THEOREM X = X'
BY Isa

=======================================================================
