------------- MODULE instance_constant_level_stest --------------

\* M!T holds because c is a constant.  Its primed theorem makes M a
\* nonconstant module, so c must still be replaced by a constant expression.
\* Otherwise c <- x proves x' = x from I!T.  The theorem is false: it fails for
\* a step from x = 0 to x = 1.  SANY rejects the INSTANCE with "The level
\* of the expression or operator substituted for 'c' must be at most 0."

---- MODULE M ----
CONSTANT c
THEOREM T == c' = c
OBVIOUS
====

VARIABLE x

I == INSTANCE M WITH c <- x

THEOREM x' = x
BY I!T

=================================================================
known: https://github.com/tlaplus/tlapm/issues/213
