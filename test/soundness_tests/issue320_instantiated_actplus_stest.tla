------------- MODULE issue320_instantiated_actplus_stest --------------

\* https://github.com/tlaplus/tlapm/issues/320
\* Instantiation does not distribute over -+-> (Specifying Systems,
\* Section 17.8), but tlapm substitutes into its arguments.  In Inner, every
\* prefix can be extended to satisfy <>(x # y) but none to satisfy FALSE, so
\* P equals FALSE, and so does I!P.  With x <- z, y <- z, <>(z # z) -+-> FALSE
\* equals TRUE, so the theorem is false.

EXTENDS TLAPS

VARIABLE z

---- MODULE Inner ----
VARIABLES x, y
P == <>(x # y) -+-> FALSE
====

I == INSTANCE Inner WITH x <- z, y <- z

THEOREM I!P <=> (<>(z # z) -+-> FALSE)
BY PTL DEF I!P

==============================================================================
known: https://github.com/tlaplus/tlapm/issues/320
