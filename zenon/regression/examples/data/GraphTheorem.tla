---------------------------- MODULE GraphTheorem ----------------------------
EXTENDS Sets, TLAPS

\* CONSTANT Nodes
\* ASSUME NodesFinite == IsFiniteSet(Nodes)

ASSUME Cooper == TRUE
   (*{by (cooper) }*)

Edges(Nodes) == { {m[1], m[2]} : m \in Nodes \X Nodes }
  (*************************************************************************)
  (* The definition we want is                                             *)
  (*                                                                       *)
  (*    Edges == {{m, n} : m, n \in Nodes}                                 *)
  (*                                                                       *)
  (* However, this construct wasn't supported by Zenon/Isabelle            *)
  (* on 7 June 2009.                                                       *)
  (*************************************************************************)

\* CONSTANT Edges

(***************************************************************************)
(* Proved 7 June 2009.  This was made very difficult by a bug in WITNESS.  *)
(* However, it reveals that Zenon/Isabelle are very bad ad finding their   *)
(* own witnesses.                                                          *)
(*                                                                         *)
(* Note that this theorem is needed only because we can't use the proper   *)
(* definition of Edges.                                                    *)
(*                                                                         *)
(* Reproved 10 June 2009 after removing the Nodes parameter and making it  *)
(* an argument of the operators.  Just made the obvious changes to the     *)
(* proof and it worked.                                                    *)
(***************************************************************************)
THEOREM EdgesAxiom == \A Nodes :
                       /\ \A m, n \in Nodes : {m, n} \in Edges(Nodes)
                       /\ \A e \in Edges(Nodes) :
                            \E m, n \in Nodes : e = {m, n}
<1>0 SUFFICES ASSUME NEW Nodes
              PROVE  /\ \A m, n \in Nodes : {m, n} \in Edges(Nodes)
                     /\ \A e \in Edges(Nodes) :
                          \E m, n \in Nodes : e = {m, n}
 BY <1>0
<1>1. ASSUME NEW m \in Nodes,
             NEW n \in Nodes
      PROVE  {m, n} \in Edges(Nodes)
   <2>1. DEFINE f == <<m, n>>
   <2>2. f \in Nodes \X Nodes
    OBVIOUS
   <2> HIDE DEF f              \* Another case where HIDE is needed
   <2>3. {f[1], f[2]} \in Edges(Nodes)
     BY <2>2 DEF Edges
\* XXXX This was fixed by a hack.  It wouldn't work if Edges
\* XXXX were a subset of Nodes \X Nodes \X Nodes
   <2> USE DEF f
   <2>4. QED
     BY <2>3
<1>2. ASSUME NEW e \in Edges(Nodes)
      PROVE  \E m, n \in Nodes : e = {m, n}
  <2>1. PICK  f \in Nodes \X Nodes : e = {f[1], f[2]}
    BY DEF Edges
\* XXXX This was fixed by a hack.  It wouldn't work if Edges
\* XXXX were a subset of Nodes \X Nodes \X Nodes
  <2>2. f[1] \in Nodes /\ f[2] \in Nodes
    OBVIOUS
  <2>3. \E n \in Nodes : e = {f[1], n}
    BY <2>1, <2>2
  <2>4. \E m \in Nodes : \E n \in Nodes : e = {m ,n}
    <3>1. USE <2>2, <2>3
    <3>2. WITNESS f[1] \in Nodes
    <3>3. QED
      OBVIOUS
  <2>5. QED
    BY <2>4
<1>3. QED
  BY <1>1, <1>2
-------------------------------------------------------
THEOREM EdgesFinite == \A Nodes :
                          IsFiniteSet(Nodes) => IsFiniteSet(Edges(Nodes))
PROOF OMITTED
  (*************************************************************************)
  (* To prove this, we need the rule                                       *)
  (*                                                                       *)
  (*      THEOREM ASSUME NEW P(_), NEW S,                                  *)
  (*                     IsFiniteSet(S)                                    *)
  (*              PROVE  IsFiniteSet({P(x) : x \in S})                     *)
  (*                                                                       *)
  (* By the prover can't yet handle the ASSUME NEW P(_).                   *)
  (*************************************************************************)

NonLoopEdges(Nodes) == {e \in Edges(Nodes) : Cardinality(e) = 2}
SimpleGraphs(Nodes) == SUBSET NonLoopEdges(Nodes)
Degree(n, G) == Cardinality ({e \in G : n \in e})

THEOREM AtLeastTwo == ASSUME NEW S,
                             IsFiniteSet(S),
                             Cardinality(S) > 1
                      PROVE  \E x, y \in S : x # y
<1>1. CASE TRUE
      <4>1. DEFINE N == Cardinality(S)
      <4>2. Cardinality(S) \in Nat
        BY CardinalityInNat
      <4>5. /\ 1 \in 1..N
            /\ 2 \in 1..N
            /\ 1 # 2
        <5>1. /\ \A i \in Nat : i > 1 => /\ 1 \in 1..i
                                         /\ 2 \in 1..i
              /\ 1 # 2
          BY Cooper
        <5>2. QED
          BY <5>1, <4>2
      <4>6. PICK f : IsBijection(f, 1..N, S)
        BY <4>2, CardinalityAxiom
      <4>7. /\ f[1] \in S
            /\ f[2] \in S
            /\ f[1] # f[2]
        BY <4>5, <4>6 DEF IsBijection
      <4>8. QED
        BY <4>7
<1>2. QED
  BY <1>1

------------------------------------------------------------------
(***************************************************************************)
(* Here's an informal proof of the following theorem                       *)
(*                                                                         *)
(* THEOREM For any finite graph G with no self loops and with more than 1  *)
(* node, there exist two nodes with the same degree.                       *)
(*                                                                         *)
(* <1>1. It suffices to assume G has at most one node with degree 0.       *)
(*   PROOF The theorem is obviously true if G has two nodes with degree 0. *)
(* <1>2. Let H be the subgraph of G obtained by eliminating all            *)
(*       nodes of degree 0.                                                *)
(* <1>3. H as at least 1 node.                                             *)
(*   PROOF By <1>1 and the assumption that G has                           *)
(*       more than one node.                                               *)
(* <1>4. The degree of every node in H is greater than 1 and less than     *)
(*       Cardinality(H).                                                   *)
(*   <2>1. For any node n of H, Degree(n, H) > 0                           *)
(*     PROOF by definition of H.                                           *)
(*         Degree(n, H) < Cardinality                                      *)
(*                                                                         *)
(* <1>5. QED                                                               *)
(*   BY <1>4 and the pigeonhole principle                                  *)
(*                                                                         *)
(* The formal proof doesn't follow exactly this structure.                 *)
(***************************************************************************)
THEOREM
 \A Nodes :
  /\ IsFiniteSet(Nodes)
  /\ Cardinality(Nodes) > 1
  =>
  \A G \in SimpleGraphs(Nodes) :
         \E m, n \in Nodes : /\ m # n
                             /\ Degree(m, G) = Degree(n, G)
(***************************************************************************)
(* Proved on 15 June in 45 Seconds: PM 30 sec, Isabelle 15 sec             *)
(***************************************************************************)
<1>1. SUFFICES ASSUME NEW Nodes,
                    IsFiniteSet(Nodes),
                    Cardinality(Nodes) > 1
               PROVE  \A G \in SimpleGraphs(Nodes) :
                        \E m, n \in Nodes : /\ m # n
                                            /\ Degree(m, G) = Degree(n, G)
  BY <1>1
<1>2. SUFFICES ASSUME NEW G \in SimpleGraphs(Nodes)
               PROVE  \E m, n \in Nodes : /\ m # n
                                          /\ Degree(m, G) = Degree(n, G)
 BY <1>2
<1>3. SUFFICES ASSUME \A m, n \in Nodes :
                         (m # n) => Degree(m, G) # Degree(n, G)
               PROVE  FALSE
  BY <1>3
<1>4. CASE \E m, n \in Nodes : /\ Degree(m, G) = 0
                               /\ Degree(n, G) = 0
                               /\ (m # n)
  BY <1>3, <1>4
<1>5. CASE \A m, n \in Nodes : /\ Degree(m, G) = 0
                               /\ Degree(n, G) = 0
                               => (m = n)
  <2>1. /\ G \subseteq NonLoopEdges(Nodes)
        /\ \A e \in G : /\ e \in Edges(Nodes)
                        /\ Cardinality(e) = 2
    BY DEF SimpleGraphs, NonLoopEdges
  <2>2. DEFINE Isolated  == {n \in Nodes : Degree(n, G) = 0}
               Connected == Nodes \ Isolated
  <2>2a. /\ IsFiniteSet(Connected)
         /\ Cardinality(Connected) \in Nat
    BY FiniteSubset, CardinalityInNat, <1>1
  <2>3. /\ IsFiniteSet(Isolated)
        /\ Cardinality(Isolated) \in Nat
        /\ Cardinality(Isolated) \leq 1
    <3>1. IsFiniteSet(Isolated)
      BY FiniteSubset, <1>1
    <3>2. Cardinality(Isolated) \in Nat
      BY <3>1, CardinalityInNat
    <3>3. CASE Cardinality(Isolated) > 1
      <4>1. PICK x \in Isolated, y \in Isolated : x # y
        BY AtLeastTwo, <3>1, <3>3, Blast
      <4>2. /\ x \in Nodes /\ Degree(x, G) = 0
            /\ y \in Nodes /\ Degree(y, G) = 0
        OBVIOUS
      <4>3. QED
        BY <1>5, <4>1, <4>2
    <3>4. QED
      <4>1. \A i \in Nat : (i \leq 1) \/ (i > 1)
        BY Cooper
      <4>2. QED
        BY <3>1, <3>2, <3>3, <4>1
  <2>4. Cardinality(Connected) \geq 1
   <3>2. /\ Connected \cap Isolated = {}
         /\ Connected \cup Isolated = Nodes
     BY SetEquality
   <3>3. Cardinality(Nodes) = Cardinality(Connected) + Cardinality(Isolated)
                                - Cardinality(Connected \cap Isolated)
    <4>1. Cardinality(Connected \cup Isolated)
              = Cardinality(Connected) + Cardinality(Isolated)
                                - Cardinality(Connected \cap Isolated)
     <5> HIDE DEF Connected, Isolated
          \* Without hide, Not handled by Zenon, takes Isabelle 50 seconds
     <5>1. QED
       BY <2>3, <2>2a, CardinalityUnion
    <4>2. QED
      BY <4>1, <3>2
   <3>4. Cardinality(Connected \cap Isolated) = 0
     BY <3>2, CardinalityZero
   <3>5. \A i, j \in Nat : /\ j \leq 1
                           /\ i + j - 0 > 1
                           => i \geq 1
     BY Cooper
   <3>7. QED
     BY <2>3, <2>2a, <3>4, <3>3, <3>5, <1>1
  <2>5. \A e \in G : \A n \in e : /\ n \in Connected
                                  /\ Degree(n, G) # 0
    <3>1. SUFFICES ASSUME NEW e \in G,
                          NEW n \in e
                   PROVE  /\ n \in Nodes
                          /\ n \notin Isolated
      BY <3>1
    <3>2. n \in Nodes
      <4>1. PICK p, q \in Nodes : e = {p, q}
        <5>1. e \in Edges(Nodes)
          BY <2>1
        <5>2. QED
          BY <5>1, EdgesAxiom
      <4>2 n \in {p,q}
        BY <4>1
      <4>3. n = p \/ n = q
        BY <4>2
      <4>4. QED
        BY <4>3
    <3>3. Degree(n, G) # 0
      <4>1. {ee \in G : n \in ee} # {}
        OBVIOUS
      <4>2. IsFiniteSet({ee \in G : n \in ee})
        <5>1. IsFiniteSet(Edges(Nodes))
          BY EdgesFinite, <1>1
        <5>2. IsFiniteSet(NonLoopEdges(Nodes))
            BY  <5>1, FiniteSubset  DEF NonLoopEdges
        <5>3. IsFiniteSet(G)
          BY <5>2, FiniteSubset DEF SimpleGraphs
        <5>4. QED
          BY <5>3, FiniteSubset
      <4>3. Cardinality({ee \in G : n \in ee}) # 0
        BY <4>2, CardinalityZero
      <4>4. QED
         BY <4>3 DEF Degree
    <3>4. QED
      BY <3>2, <3>3
  <2>6. \A n \in Connected : /\ Degree(n, G) \in Nat
                             /\ Degree(n, G) < Cardinality(Connected)
   <3>1. \A n \in Nodes : Degree(n, G) \in Nat
     <4>1. Edges(Nodes) \subseteq SUBSET Nodes
       <5>1. SUFFICES ASSUME NEW e,
                             e \in  Edges(Nodes),
                             NEW n,
                             n \in e
                      PROVE  n \in Nodes
         BY <5>1
       <5>2. PICK f \in Nodes \X Nodes : e = {f[1], f[2]}
         BY <5>1 DEF Edges
       <5>3. f[1] \in Nodes /\ f[2] \in Nodes
\* THIS works with PROOF OBVIOUS, but it takes Isabelle 3min 11sec
\*         <6> \A S : \A g \in S \X S : g[1] \in S /\ g[2] \in S
\*         THIS DOESN'T HELP
(* HIDEing formulas is not allowed by SANY.
         <6> HIDE \A m, nn \in Nodes : /\ Degree(m, G) = 0
                                       /\ Degree(nn, G) = 0
                                       => (m = nn) ,
                  \A m, nn \in Nodes :
                         (m # nn) => Degree(m, G) # Degree(nn, G)
*)
         <6>1. QED
          PROOF OBVIOUS
       <5>4. n = f[1] \/ n = f[2]
         BY <5>1, <5>2
       <5>5. QED
         BY <5>3, <5>4
     <4>2. IsFiniteSet(Edges(Nodes))
       <5>1. IsFiniteSet(SUBSET Nodes)
         BY SubsetsFinite, <1>1
       <5>2. QED
         BY <4>1, <5>1, FiniteSubset
     <4>3. NonLoopEdges(Nodes) \subseteq Edges(Nodes)
       BY DEF NonLoopEdges
     <4>4. IsFiniteSet(NonLoopEdges(Nodes))
       BY <4>2, <4>3, FiniteSubset
     <4>5. IsFiniteSet(G)
       BY <2>1, <4>4, FiniteSubset
     <4>6. \A n \in Nodes : {e \in G : n \in e} \subseteq G
       OBVIOUS
     <4>7. \A n \in Nodes : IsFiniteSet({e \in G : n \in e})
       BY <4>5, <4>6, FiniteSubset
     <4>8. QED
       BY <4>7, CardinalityAxiom DEF Degree
   <3>2. ASSUME NEW e \in G,
                NEW n \in e
         PROVE  \E m \in Connected : n # m /\ e = {m, n}
     <4>1. e \in NonLoopEdges(Nodes)
       BY DEF SimpleGraphs
     <4>2. /\ e \in Edges(Nodes)
           /\ Cardinality(e) = 2
        BY <4>1 DEF NonLoopEdges
     <4>3. PICK m \in Nodes, p \in Nodes : e = {m, p}
       BY <4>2, EdgesAxiom
     <4>4. m # p
       <5>1. SUFFICES ASSUME m = p
                      PROVE  FALSE
         BY <5>1
       <5>2. e = {m}
         BY <5>1, <4>3
       <5>3. Cardinality(e) = 1
         BY <5>2, CardinalityOne
       <5>4. (1 # 2)
         BY Cooper
       <5>5. QED
         BY <5>3, <4>2, <5>4
     <4>4a. m \in Connected /\ p \in Connected
       BY <2>5, <4>3
     <4>5. n \in {m, p}
       BY <4>3
     <4> USE <4>4a
     <4>6. CASE n = m
       <5>1. WITNESS p \in Connected
       <5>2. QED
         BY <4>4, <4>6, <4>3
     <4>7. CASE n = p
       <5>1. WITNESS m \in Connected
       <5>2. QED
         BY <4>4, <4>7, <4>3
     <4>8. QED
       BY <4>5, <4>6, <4>7
   <3>3. SUFFICES ASSUME NEW n \in Connected
                  PROVE  Cardinality({e \in G : n \in e}) <
                            Cardinality(Connected)
     BY <3>1, <3>3 DEF Degree
   <3> DEFINE  nEdges == {e \in G : n \in e}
               PossibleNEdges == {{m, n} : m \in Connected \ {n}}
   <3>4. /\ nEdges \subseteq PossibleNEdges
         /\ IsFiniteSet(PossibleNEdges)
         /\ Cardinality(nEdges) \in Nat (* XXX NOT PROVED **)
         /\ Cardinality(nEdges) \leq Cardinality(PossibleNEdges)
     <4>1. nEdges \subseteq PossibleNEdges
       <5>1. SUFFICES ASSUME NEW e \in nEdges
                      PROVE  \E m \in Connected \ {n} : e = {m, n}
         BY <5>1
       <5>2. e \in G
         OBVIOUS
       <5>3. PICK m \in Connected : n # m /\ e = {m, n}
         BY <5>2, <3>2
       <5>4. m \in Connected \ {n}
         BY <5>3
       <5>5. QED
         BY <5>3, <5>4
     <4>2. PossibleNEdges \subseteq SUBSET Nodes
       <5>1. ASSUME NEW e \in PossibleNEdges
             PROVE  e \subseteq Nodes
        <6>1. PICK m \in Connected \ {n} : e = {m, n}
          PROOF OBVIOUS
        <6>2. Connected \ {n} \subseteq Nodes
          OBVIOUS
        <6>3. n \in Nodes
          BY <6>2
        <6>4. QED
          BY <6>3
       <5>2. QED
         BY <5>1
     <4>3. IsFiniteSet(SUBSET Nodes)
       BY SubsetsFinite, <1>1
     <4>4. IsFiniteSet(PossibleNEdges)
       BY <4>2, <4>3, FiniteSubset
     <4>5. IsFiniteSet(nEdges)
        BY <4>1, <4>4, FiniteSubset
     <4>6. Cardinality(nEdges) \in Nat
       BY <4>5, CardinalityInNat
     <4>7. Cardinality(nEdges) \leq Cardinality(PossibleNEdges)
       BY <4>1, <4>4, FiniteSubset
     <4>8. QED
       BY <4>1, <4>4, <4>6, <4>7
   <3> DEFINE NC == Cardinality(Connected \ {n})
   <3>5. /\ IsFiniteSet(Connected \ {n})
         /\ NC \in Nat
         /\ NC < Cardinality(Connected)
     <4>1. /\ IsFiniteSet(Connected)
           /\ Cardinality(Connected) \in Nat
       BY FiniteSubset, CardinalityInNat
     <4>2. /\ IsFiniteSet(Connected \ {n})
           /\ NC = Cardinality(Connected) - 1
       BY <4>1, CardinalityMinusOne
     <4>3. NC \in Nat
       BY <4>2, CardinalityInNat
     <4>4. \A i, j \in Nat : i = j - 1 => i < j
       BY Cooper
     <4>5. QED
       BY <4>1, <4>2, <4>3, <4>4
   <3>6. PICK f : IsBijection(f, 1..NC, Connected \ {n})
     BY <3>5, CardinalityAxiom
   <3>7. DEFINE g == [i \in 1..NC |-> {n, f[i]}]
   <3>8. IsBijection(g, 1..NC, PossibleNEdges)
     <4>1. g  \in [1..NC -> PossibleNEdges]
       <5>1. SUFFICES ASSUME NEW i \in 1..NC
                      PROVE  g[i] \in PossibleNEdges
         BY <5>1
       <5>2. SUFFICES \E m \in Connected \ {n} : g[i] = {m, n}
         BY <5>2
       <5>3. SUFFICES \E m \in Connected \ {n} : {f[i], n} = {m, n}
         BY <5>3
       <5> f[i] \in Connected \ {n}
         BY <3>6 DEF IsBijection
       <5>5. WITNESS f[i] \in Connected \ {n}
       <5>6. QED
         OBVIOUS
     <4>2. ASSUME NEW i \in 1..NC,
                  NEW j \in 1..NC,
                  (i # j)
           PROVE  g[i] # g[j]
       <5>1. /\ g[i] = {n, f[i]}
             /\ g[j] = {n, f[j]}
         OBVIOUS
       <5>2. f[i] # f[j]
         BY <3>6, <4>2 DEF IsBijection
       <5>3. QED
         BY <5>1, <5>2
     <4>3. ASSUME NEW y \in PossibleNEdges
           PROVE  \E i \in 1..NC : g[i] = y
       <5>1. PICK m \in Connected \ {n} : y = {m, n}
         OBVIOUS
       <5>2. PICK i \in 1..NC : f[i] = m
         BY <3>6 DEF IsBijection
       <5>3. g[i] = y
         BY <5>2, <5>1
       <5>4. QED
         BY <5>3
     <4>4. QED
       BY <4>1, <4>2, <4>3 DEF IsBijection
   <3>9. NC = Cardinality(PossibleNEdges)
    <4> HIDE DEF g, nEdges, PossibleNEdges, NC
    <4>2. QED
      BY <3>4, <3>5, CardinalityAxiom, <3>8
   <3>10. QED
    <4>1. \A i, j, k \in Nat : i \leq j /\ j < k => i < k
      BY Cooper
    <4> HIDE DEF NC, g, PossibleNEdges
    <4>2. QED
      BY <4>1, <3>4, <3>5, <3>9, <2>2a
         (******************************************************************)
         (* WITH i <- Cardinality(nEdges),                                 *)
         (*      j <- NC = Cardinality(PossibleNEdges)                     *)
         (*      k <- Cardinality(Connected)                               *)
         (******************************************************************)
\* XXX
  <2>7. DEFINE f == [n \in Connected |-> Degree(n, G)]
  <2>8. f \in [Connected -> 1 .. (Cardinality(Connected)-1)]
    <3> DEFINE CC == Cardinality(Connected)
    <3>1. SUFFICES ASSUME NEW n \in Connected
                   PROVE  f[n] \in 1 .. (CC-1)
      BY <3>1
    <3>2. /\ Degree(n, G) \in Nat
          /\ Degree(n, G) < Cardinality(Connected)
          /\ Degree(n, G) # 0
      BY <2>6
    <3>3. /\ Degree(n, G) \in Int
          /\ 1 \leq Degree(n, G)
          /\ Degree(n, G) \leq CC-1
      <4>1. /\ \A i \in Nat : /\ i \in Int
                              /\ i # 0 => 1 \leq i
            /\ \A i, j \in Nat : i < j => i \leq j-1
        BY Cooper
      <4>2. QED
        BY <3>2, <4>1, <2>2a
    <3>4. QED
       BY <3>3, DotDotDef
  <2>9. \E m, n \in Connected: m # n /\ f[m] = f[n]
    <3> HIDE DEF Connected, f
    <3> DEFINE CC1 == Cardinality(Connected)-1
    <3>1. /\ IsFiniteSet(1..CC1)
          /\ Cardinality(1..CC1) = CC1
      <4>1. /\ 1 \in Int
            /\ CC1 \in Int
            /\ CC1+1  \geq 1
        <5>1. /\ 1 \in Int
              /\ \A i \in Nat : /\ i - 1 \in Int
                                /\ (i-1)+1 = i
                                /\ i-1+1 = i
          BY Cooper
        <5>2. QED
          BY <5>1, <2>2a, <2>4
      <4>1a. CC1-1+1 = CC1
        <5>1. \A i \in Int : i-1+1 = i
          BY Cooper
        <5>2. QED
          BY <5>1, <4>1
      <4>2. (1 \leq CC1+1)
        <5>1. \A i \in Int : i+1 \geq 1 => 1 \leq i+1
          BY Cooper
        <5>2. QED
          BY <4>1, <5>1
      <4>3. QED
        BY <4>1, <4>1a, <4>2, IntervalCardinality
    <3>2. Cardinality(1..CC1) < Cardinality(Connected)
      <4>1. \A i \in Nat : i-1 < i
        BY Cooper
      <4>2. QED
        BY <4>1, <3>1, <2>2a
    <3>3. QED
      <4> DEFINE T == 1..CC1
      <4>0. /\ IsFiniteSet(T)
            /\ Cardinality(T) < Cardinality(Connected)
        BY <3>1, <3>2
      <4>1. \A gg \in [Connected -> T] :
                \E x, y \in Connected :
                     x # y /\ gg[x] = gg[y]
        BY <2>2a, <4>0, PigeonHole
      <4>3. QED
         BY <2>8, <4>1
  <2>10. QED
    BY <1>3, <1>5, <2>9
<1>. QED
  BY <1>4, <1>5
=============================================================================
