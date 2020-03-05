---- MODULE testsubset ----

THEOREM test ==
  ASSUME NEW A, NEW B,
         A \subseteq B
  PROVE \A x : x \in A => x \in B
OBVIOUS

====
