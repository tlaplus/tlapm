---- MODULE testbool ----

THEOREM foo ==
  ASSUME NEW x \in BOOLEAN
  PROVE x = TRUE \/ x = FALSE
OBVIOUS

====
