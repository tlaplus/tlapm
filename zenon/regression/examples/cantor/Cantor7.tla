(* Contributed by Damien Doligez *)

-------------- MODULE Cantor7 ------------------
THEOREM cantor ==
  \A S, f :
    \E A \in SUBSET S :
      \A x \in S :
        f [x] # A
PROOF
  <1> SUFFICES ASSUME
        NEW S,
        NEW f
      PROVE \E A \in SUBSET S : \A x \in S : f[x] # A
    BY DEF cantor
  <1> WITNESS { z \in S : z \notin f[z] } \in SUBSET S
  <1> QED OBVIOUS
===============================================
