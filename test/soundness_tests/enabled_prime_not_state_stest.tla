------------- MODULE enabled_prime_not_state_stest --------------

\* False. ENABLED (x' = 1) is TRUE, not the state predicate x = 1.

EXTENDS TLAPS

VARIABLE x

THEOREM (ENABLED (x' = 1)) <=> (x = 1)
BY Isa

============================================================
