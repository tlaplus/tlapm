---------------------------- MODULE GraphTheorem ----------------------------
EXTENDS FiniteSetTheorems, FunctionTheorems, TLAPS

Edges(Nodes) == { {m[1], m[2]} : m \in Nodes \X Nodes }
  (*************************************************************************)
  (* The definition we want is                                             *)
  (*                                                                       *)
  (*    Edges(Nodes) == {{m, n} : m, n \in Nodes}                          *)
  (*                                                                       *)
  (* However, this construct isn't supported by TLAPS yet.                 *)
  (*************************************************************************)

LEMMA EdgesAxiom == \A Nodes :
                       /\ \A m, n \in Nodes : {m, n} \in Edges(Nodes)
                       /\ \A e \in Edges(Nodes) :
                            \E m, n \in Nodes : e = {m, n}
BY IsaM("force") DEF Edges

-------------------------------------------------------
LEMMA EdgesFinite ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes)
  PROVE  IsFiniteSet(Edges(Nodes))
<1>1. IsFiniteSet(Nodes \X Nodes)
  BY FS_Product
<1>2. [m \in Nodes \X Nodes |-> {m[1], m[2]}] \in Surjection(Nodes \X Nodes, Edges(Nodes))
  BY Fun_IsSurj, Zenon DEF Edges
<1>. QED  BY <1>1, <1>2, FS_Surjection

NonLoopEdges(Nodes) == {e \in Edges(Nodes) : Cardinality(e) = 2}
SimpleGraphs(Nodes) == SUBSET NonLoopEdges(Nodes)
Degree(n, G) == Cardinality ({e \in G : n \in e})

LEMMA NLEdgeElements ==
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW e \in NonLoopEdges(Nodes)
  PROVE  \E m,n \in Nodes : m # n /\ e = {m,n}
<1>. PICK m,n \in Nodes : e = {m,n}
  BY EdgesAxiom DEF NonLoopEdges
<1>. SUFFICES ASSUME m = n PROVE FALSE
  OBVIOUS
<1>. QED
  BY FS_Singleton, Isa DEF NonLoopEdges

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
(* <1>4. Let n be a node in H. Then its degree is at least 1 and           *)
(*       less than Cardinality(H).                                         *)
(*   <2>1. Degree(n, G) > 0                                                *)
(*     PROOF by definition of H.                                           *)
(*   <2>2. Degree(n, G) < Cardinality(H)                                   *)
(*     PROOF Any edge containing n has a node in H as its other vertex.    *)
(* <1>5. QED                                                               *)
(*   BY <1>4 and the pigeonhole principle                                  *)
(*                                                                         *)
(* The formal proof doesn't follow exactly this structure.                 *)
(***************************************************************************)
THEOREM
  ASSUME NEW Nodes, IsFiniteSet(Nodes), Cardinality(Nodes) > 1,
         NEW G \in SimpleGraphs(Nodes)
  PROVE  \E m, n \in Nodes : /\ m # n
                             /\ Degree(m, G) = Degree(n, G)
<1>1. SUFFICES ASSUME \A m, n \in Nodes :
                         (m # n) => Degree(m, G) # Degree(n, G)
               PROVE  FALSE
  BY <1>1
<1>2. CASE \E m, n \in Nodes : /\ Degree(m, G) = 0
                               /\ Degree(n, G) = 0
                               /\ (m # n)
  BY <1>1, <1>2
<1>3. CASE \A m, n \in Nodes : /\ Degree(m, G) = 0
                               /\ Degree(n, G) = 0
                               => (m = n)
  <2>1. /\ G \subseteq NonLoopEdges(Nodes)
        /\ \A e \in G : /\ e \in Edges(Nodes)
                        /\ Cardinality(e) = 2
    BY DEF SimpleGraphs, NonLoopEdges
  <2>. DEFINE Isolated  == {n \in Nodes : Degree(n, G) = 0}
              Connected == Nodes \ Isolated
  <2>2. /\ IsFiniteSet(Connected)
        /\ Cardinality(Connected) \in Nat
    BY FS_Subset, FS_CardinalityType
  <2>3. /\ IsFiniteSet(Isolated)
        /\ Cardinality(Isolated) \in Nat
        /\ Cardinality(Isolated) \leq 1
    <3>1. IsFiniteSet(Isolated) /\ Cardinality(Isolated) \in Nat
      BY FS_Subset, FS_CardinalityType
    <3>2. CASE Cardinality(Isolated) > 1
      <4>1. PICK x \in Isolated, y \in Isolated : x # y
        BY <3>1, <3>2, FS_CardinalityType, CVC4 DEF ExistsBijection, Bijection, Injection
      <4>. QED
        BY <1>3, <4>1
    <3>3. QED
      BY <3>1, <3>2
  <2>4. Cardinality(Connected) \geq 1
    BY <2>2, <2>3, Connected \cap Isolated = {}, Connected \cup Isolated = Nodes, FS_Union, FS_EmptySet
  <2>5. ASSUME NEW e \in G, NEW n \in e
        PROVE  /\ n \in Nodes
               /\ n \notin Isolated
    <3>1. n \in Nodes
      BY <2>1, EdgesAxiom
    <3>2. Degree(n, G) # 0
      <4>2. IsFiniteSet({ee \in G : n \in ee})
        BY EdgesFinite, FS_Subset, Zenon DEF NonLoopEdges, SimpleGraphs
      <4>3. Cardinality({ee \in G : n \in ee}) # 0
        BY <4>2, FS_EmptySet, Isa
      <4>. QED
        BY <4>3 DEF Degree
    <3>. QED  BY <3>1, <3>2
  <2>6. \A n \in Connected : /\ Degree(n, G) \in Nat
                             /\ Degree(n, G) < Cardinality(Connected)
    <3>1. \A n \in Nodes : Degree(n, G) \in Nat
      BY EdgesFinite, FS_Subset, FS_CardinalityType DEF NonLoopEdges, SimpleGraphs, Degree
    <3>2. ASSUME NEW e \in G,
                 NEW n \in e
          PROVE  \E m \in Connected : n # m /\ e = {m, n}
      BY <2>5, NLEdgeElements DEF SimpleGraphs
    <3>3. SUFFICES ASSUME NEW n \in Connected
                   PROVE  Cardinality({e \in G : n \in e}) < Cardinality(Connected)
      BY <3>1, <3>3 DEF Degree
    <3> DEFINE  nEdges == {e \in G : n \in e}
                PossibleNEdges == {{m, n} : m \in Connected \ {n}}
    <3>4. /\ Cardinality(nEdges) \in Nat
          /\ Cardinality(nEdges) \leq Cardinality(PossibleNEdges)
      <4>1. IsFiniteSet(Connected \ {n})
        BY FS_Subset
      <4>2. IsFiniteSet(PossibleNEdges)
        BY <4>1, FS_Image, Isa
      <4>. QED  BY <4>2, <3>2, FS_Subset, FS_CardinalityType
    <3> DEFINE NC == Cardinality(Connected \ {n})
    <3>5. /\ IsFiniteSet(Connected \ {n})
          /\ NC \in Nat
          /\ NC < Cardinality(Connected)
      BY FS_Subset, FS_CardinalityType
    <3>. DEFINE f == [m \in Connected \ {n} |-> {m,n}]
    <3>6. f \in Bijection(Connected \ {n}, PossibleNEdges)
      BY Fun_IsBij, Zenon
    <3>7. NC = Cardinality(PossibleNEdges)
      BY <3>5, <3>6, FS_Bijection DEF ExistsBijection
    <3>. QED  BY <2>2, <3>4, <3>5, <3>7
  <2>7. DEFINE f == [n \in Connected |-> Degree(n, G)]
  <2>8. f \in [Connected -> 1 .. (Cardinality(Connected)-1)]
    BY <2>6, <2>2
  <2>9. \E m, n \in Connected: m # n /\ f[m] = f[n]
    <3> DEFINE CC1 == Cardinality(Connected)-1
    <3>1. /\ IsFiniteSet(1 .. CC1)
          /\ Cardinality(1 .. CC1) < Cardinality(Connected)
      BY <2>2, <2>4, FS_Interval
    <3> QED  BY <2>2, <2>4, <2>8, <3>1, FS_PigeonHole, Isa
  <2>. QED  BY <1>1, <1>3, <2>9
<1>. QED  BY <1>2, <1>3
=============================================================================
