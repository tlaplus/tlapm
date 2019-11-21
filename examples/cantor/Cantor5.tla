(* Contributed by Damien Doligez *)

-------------- MODULE Cantor5 ------------------
THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
<1>1. ASSUME NEW S, NEW f
      PROVE  \E A \in SUBSET S : \A x \in S : f[x] # A
  <2> WITNESS { z \in S : z \notin f[z] } \in SUBSET S
  <2> QED OBVIOUS
<1> QED BY <1>1
===============================================
