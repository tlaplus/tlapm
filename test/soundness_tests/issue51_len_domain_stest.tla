------------- MODULE issue51_len_domain_stest --------------

\* https://github.com/tlaplus/tlapm/issues/51
\* Default SMT encoding variant of issue51_len_domain_oldsmt_stest.
\* Len(f) is a CHOOSE without a witness for a function f on Nat, so its
\* value is unspecified and may lie in Nat.  The assumptions are
\* consistent, and the theorem is false.

EXTENDS Naturals, Sequences, TLAPS

THEOREM ASSUME NEW f, DOMAIN f = Nat, Len(f) \in Nat
        PROVE  FALSE
BY SMT

============================================================
