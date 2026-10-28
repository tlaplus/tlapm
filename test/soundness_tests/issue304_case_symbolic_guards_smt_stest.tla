------------- MODULE issue304_case_symbolic_guards_smt_stest --------------

\* https://github.com/tlaplus/tlapm/issues/304
\* With p and q both true, both CASEs choose from {1, 2} under the same
\* predicate, so they are equal and the theorem is false.  Lowering CASE
\* to an ordered IF/ite makes the two sides distinct and proves it.

EXTENDS Naturals, TLAPS

THEOREM ASSUME NEW p, NEW q, p, q
        PROVE  (CASE p -> 1 [] q -> 2 [] OTHER -> 3)
                 # (CASE q -> 2 [] p -> 1 [] OTHER -> 3)
BY SMT

===========================================================================
known: https://github.com/tlaplus/tlapm/issues/304
