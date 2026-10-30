------------- MODULE fresh_operator_args_stest --------------

\* The action frontend must not abstract an application of a declared
\* STATE operator without its constant arguments: F(1) and F(2) would
\* become the same term.  The theorem is false: F may differ on 1 and 2.

THEOREM ASSUME NEW STATE F(_) PROVE F(1) = F(2)
OBVIOUS

============================================================
