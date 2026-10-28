------------- MODULE issue304_case_symbolic_guards_oldsmt_stest --------------

\* https://github.com/tlaplus/tlapm/issues/304
\* With p and q both true, both CASEs choose from {1, 2} under the same
\* predicate, so they are equal and the theorem is false.  The old encoding
\* lowers CASE to an ordered IF that picks the last enabled arm and proves
\* it.

EXTENDS Naturals, TLAPS

THEOREM ASSUME NEW p, NEW q, p, q
        PROVE  (CASE p -> 1 [] q -> 2 [] OTHER -> 3)
                 # (CASE q -> 2 [] p -> 1 [] OTHER -> 3)
BY SMT

==============================================================================
flags: --debug oldsmt
known: https://github.com/tlaplus/tlapm/issues/304
