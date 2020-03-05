(* Contributed by Leslie Lamport *)

-------------- MODULE Cantor3 ------------------
THEOREM cantor ==
  \A S :
    \A f \in [S -> SUBSET S] :
      \E A \in SUBSET S :
        \A x \in S :
          f [x] # A
PROOF
  <1>1. ASSUME NEW S,
               NEW f \in [S -> SUBSET S]
        PROVE  \E A \in SUBSET S :
                    \A x \in S : f [x] # A
     PROOF
       <2>1. DEFINE T == {z \in S : z \notin f [z]}
       <2>2. \A x \in S : f [x] # T
         PROOF
           <3>1. ASSUME NEW x \in S
                 PROVE  f[x] # T
             PROOF
              <4>1. CASE x \in T
                   PROOF
                     <5>1. x \notin f [x]
                           BY <4>1
                     <5>2. QED BY <5>1
              <4>2. CASE x \notin T
                    PROOF
                      <5>1. x \in f [x]
                            BY <4>2
                      <5>2. QED BY <5>1

              <4>3. QED
                    BY <4>1, <4>2
          <3>2. QED BY <3>1
      <2>3. QED
         PROOF
           <3>1. WITNESS T \in SUBSET S
           <3>2. QED BY <2>2
  <1>2. QED
         PROOF BY <1>1 DEF cantor
===============================================
