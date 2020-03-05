(* Contributed by Stephan Merz *)
(* Modified into TLA+ proof language syntax *)

-------------- MODULE Cantor4 ------------------
THEOREM cantor ==
 \A S :
   \A f \in [S -> SUBSET S] :
     \E A \in SUBSET S :
       \A x \in S :
         f [x] # A
PROOF
 <1>. USE DEF cantor
 <1>. TAKE S
 <1>. TAKE f \in [S -> SUBSET S]
 <1>. DEFINE T == {z \in S : z \notin f[z]}
 <1>1. \A x \in S : f[x] # T
       PROOF
        <2>. TAKE x \in S
        <2>1. CASE x \in T
              PROOF
               <3>1. x \notin f[x] BY <2>1
               <3>2. QED BY <3>1
        <2>2. CASE x \notin T
              PROOF
               <3>1. x \in f[x] BY <2>2
               <3>2. QED BY <3>1
        <2>3. QED BY <2>1, <2>2
 <1>. WITNESS T \in SUBSET S
 <1>. QED BY <1>1
===============================================
