(* Contributed by Damien Doligez *)

-------------- MODULE Cantor1 ------------------
THEOREM cantor ==
  \A S :
    \A f \in [S -> SUBSET S] :
      \E A \in SUBSET S :
        \A x \in S :
          f [x] # A
PROOF
  <1>. USE DEF cantor
  <1>2. TAKE S
  <1>3. TAKE f \in [S -> SUBSET S]
  <1>4. DEFINE T == { z \in S : z \notin f[z] }
  <1>5. WITNESS T \in SUBSET S
  <1>6. TAKE x \in S
  <1>7. QED BY x \in T \/ x \notin T
===============================================
