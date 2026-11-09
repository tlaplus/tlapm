------------- MODULE issue310_fresh_op_scope_isa_stest --------------

EXTENDS TLAPS

VARIABLE x

LEMMA EnabledP ==
  ASSUME NEW P(_)
  PROVE ENABLED P(x) <=> P(x)
BY ExpandENABLED

THEOREM FALSE
BY Isa, EnabledP

=====================================================================
known: https://github.com/tlaplus/tlapm/issues/310
