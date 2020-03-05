---- MODULE testbex ----

THEOREM foo ==
  ASSUME NEW S, NEW v,
         v \in S
  PROVE \E x \in S : x = x
OBVIOUS

====
