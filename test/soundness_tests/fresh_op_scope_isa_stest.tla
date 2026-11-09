------------- MODULE fresh_op_scope_isa_stest --------------

\* ENABLED P(x) <=> P(x) is valid because P(x) has no primed variables.
\* This lemma does not imply FALSE, so the theorem is invalid.

EXTENDS TLAPS

VARIABLE x

LEMMA EnabledP ==
  ASSUME NEW P(_)
  PROVE ENABLED P(x) <=> P(x)
BY ExpandENABLED

THEOREM FALSE
BY Isa, EnabledP

=====================================================================
