(* Contributed by Leslie Lamport *)

-------------- MODULE Cantor2 ------------------
THEOREM cantor ==
  \A S :
    \A f \in [S -> SUBSET S] :
      \E A \in SUBSET S :
        \A x \in S :
          f [x] # A
PROOF
  <1>1. SUFFICES ASSUME NEW S,
                        NEW f \in [S -> SUBSET S]
                 PROVE  \E A \in SUBSET S :
                          \A x \in S : f [x] # A
        BY DEF cantor
  <1>2. DEFINE T == {z \in S : z \notin f [z]}
  <1>3. SUFFICES ASSUME NEW x \in S
                 PROVE  f[x] # T
        PROOF
          <2>1. WITNESS T \in SUBSET S
          <2>2. QED
                PROOF OBVIOUS
  <1>4. CASE x \in T
        PROOF
          <2>1. x \notin f [x] BY <1>4
          <2>2. QED BY <2>1
  <1>5. CASE x \notin T
        PROOF
          <2>1. x \in f [x] BY <1>5
          <2>2. QED BY <2>1
  <1>6. QED
        PROOF BY <1>4, <1>5
===============================================
