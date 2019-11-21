------------- MODULE prime_dist_bound_var_stest --------------

VARIABLE Y

P(a,x) == IF Y THEN x ELSE x

THEOREM 1 = 2
<1>1. \A z : P(Y,z)' = z
  BY DEF P
<1>2. QED BY <1>1

===================
