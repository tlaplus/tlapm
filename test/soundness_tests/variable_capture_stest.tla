-------------- MODULE variable_capture_stest ---------------
EXTENDS Integers, TLAPS

VARIABLE x, x_prime
CONSTANT 0m, x0m
CONSTANT _ && _, a__andand(_,_)

---- MODULE bar ----
andand(a, b) == 3
====
a == INSTANCE bar

THEOREM bug ==
  \/ x_prime = x'
  \/ 0m = x0m
  \/ a__andand (2, 1) = 2 && 1
  \/ a!andand(1,2) = 1 && 2
BY SMT

===========================================
