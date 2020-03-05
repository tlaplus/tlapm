---- MODULE testball ----

THEOREM foo ==
  ASSUME NEW S
  PROVE \A x \in S : x \in S
OBVIOUS

====
