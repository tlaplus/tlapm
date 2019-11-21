(* Contributed by Damien Doligez *)

-------------- MODULE Cantor1 -----------------
THEOREM cantor ==
  \A S :
    \A f \in [S -> SUBSET S] :
      \E A \in SUBSET S :
        \A x \in S :
          f [x] # A
PROOF
  <1>1. TAKE S
  <1>2. TAKE f \in [S -> SUBSET S]
  <1>3. DEFINE T == { z \in S : z \notin f[z] }
  <1>4. WITNESS T \in SUBSET S
  <1>5. TAKE x \in S
  <1>6. QED BY x \in T \/ x \notin T
===============================================
