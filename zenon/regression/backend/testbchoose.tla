---- MODULE testbchoose ----

THEOREM foo ==
  ASSUME NEW S, NEW v, NEW P(_),
         v \in S,
         P (v)
  PROVE P (CHOOSE x \in S : P (x))
OBVIOUS

====
