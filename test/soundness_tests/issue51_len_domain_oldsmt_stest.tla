------------- MODULE issue51_len_domain_oldsmt_stest --------------

\* https://github.com/tlaplus/tlapm/issues/51
\* The old SMT encoding states its Len axioms for every value, not only
\* for sequences: Len(s) >= 0, and DOMAIN s = 1..n <=> Len(s) = n for
\* n >= 0.  Together they force DOMAIN s = 1..Len(s), which contradicts
\* DOMAIN f = Nat.  The assumptions are consistent: Len(f) is a CHOOSE
\* without a witness, so its value is unspecified and may lie in Nat.
\* The theorem is false.

EXTENDS Naturals, Sequences, TLAPS

THEOREM ASSUME NEW f, DOMAIN f = Nat, Len(f) \in Nat
        PROVE  FALSE
BY SMT

===================================================================
flags: --debug oldsmt
known: https://github.com/tlaplus/tlapm/issues/51#issuecomment-1122505326
