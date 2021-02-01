---------------------------- MODULE GraphTheoremZIP ----------------------------
EXTENDS FiniteSetTheorems, FunctionTheorems, TLAPS

(* Added *)
With(X) == TRUE (* special *)
HIDE DEF With

THEOREM UseWith == \A X : With(X)
    BY DEF With
(* \ Added *)

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
(* Proved by Zipper, not SMT.  The "With" clause is crucial *)
  BY FS_Product, Fun_IsSurj, FS_Surjection, EdgesAxiom,
     Zipper, UseWith, With([m \in Nodes \X Nodes |-> {m[1], m[2]}])

NonLoopEdges(Nodes) == {e \in Edges(Nodes) : Cardinality(e) = 2}
SimpleGraphs(Nodes) == SUBSET NonLoopEdges(Nodes)
Degree(n, G) == Cardinality ({e \in G : n \in e})

LEMMA NLEdgeElements == 
  ASSUME NEW Nodes, IsFiniteSet(Nodes),
         NEW e \in NonLoopEdges(Nodes)
  PROVE  \E m,n \in Nodes : m # n /\ e = {m,n}
<1>1 1 # 2  OBVIOUS (* TODO Implement axiom *)
<1>2 \A x : {x, x} = {x}    OBVIOUS (* TODO Apply extensionnality *)
<1> QED
  BY Zipper, <1>1, <1>2, EdgesAxiom, FS_Singleton DEF NonLoopEdges

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
    (* This should be proven in one go *)
    (*BY ZipperT(60), <1>3, FS_Subset, FS_CardinalityType
    DEF ExistsBijection, Bijection, Injection*)
    <3>1 /\ IsFiniteSet(Isolated)
         /\ Cardinality(Isolated) \in Nat
      BY FS_Subset, FS_CardinalityType
    <3>2 Cardinality(Isolated) \leq 1
      <4> \A a : (\A x : x \notin a) => a = {} OBVIOUS (* TODO Apply extensionnality *)
      <4> \A a \in Nat : (\A m, n \in 1..a : m = n) => a <= 1 OBVIOUS (* TODO Axioms for comparisons *)
      <4>1 Bijection(1..Cardinality(Isolated), Isolated) # {}
        BY <3>1, FS_CardinalityType DEF ExistsBijection
      <4>2 PICK M \in [ 1..Cardinality(Isolated) -> Isolated ] :
                \A a, b \in 1..Cardinality(Isolated) : M[a] = M[b] => a = b
        <5> HIDE DEF Isolated
        <5> QED
          (* FIXME Zipper with long timeout *)
          BY (*ZipperT(60),*) <4>1 DEF Bijection, Injection
      <4>3 \A m, n \in 1..Cardinality(Isolated) : m = n
        (* FIXME QED doesn't work without this fact *)
        BY <1>3, <4>2
      <4> QED
        BY <3>1, <4>3
    <3> QED
      BY <3>1, <3>2
  <2>4. Cardinality(Connected) \geq 1
    BY <2>2, <2>3, FS_Union, FS_EmptySet,
       Connected \cap Isolated = {},
       Connected \cup Isolated = Nodes
  <2>5. ASSUME NEW e \in G, NEW n \in e
        PROVE  /\ n \in Nodes
               /\ n \notin Isolated
    (* Zipper does it without a hint, but SMT without hints fail.
     * Maybe SMT with hint will work. *)
    BY <2>1, EdgesAxiom, EdgesFinite, FS_Subset, FS_EmptySet,
       Zipper(*, UseWith, With({ee \in G : n \in ee})*)
    DEF NonLoopEdges, SimpleGraphs, Degree
  <2>6. \A n \in Connected : /\ Degree(n, G) \in Nat
                             /\ Degree(n, G) < Cardinality(Connected)
    <3>1. \A n \in Nodes : Degree(n, G) \in Nat
      BY EdgesFinite, FS_Subset, FS_CardinalityType DEF NonLoopEdges, SimpleGraphs, Degree
    <3>2. ASSUME NEW e \in G,
                 NEW n \in e
          PROVE  \E m \in Connected : n # m /\ e = {m, n}
      (*BY <2>5, NLEdgeElements DEF SimpleGraphs*)
      <4> \A a, b, c : (\A x : x \in c <=> x = a \/ x = b) => c = {a, b} OBVIOUS
      <4>1 PICK i, j : i # j /\ e = {i, j}
        BY NLEdgeElements DEF SimpleGraphs
      <4> i \in Connected /\ j \in Connected
        BY <2>5, <4>1
      <4>2 n = i \/ n = j
        BY <4>1
      <4>3 CASE n = i
        (* FIXME Zipper with longer timeout *)
        (* This case requires set extensionnality.
         * The dual case doesn't and is solved easily. *)
        BY ZipperT(10), <4>1, <4>3
      <4>4 CASE n = j
        BY <4>1, <4>4
      <4> QED
        (*BY ONLY <4>2, <4>3, <4>4*)
        BY NLEdgeElements, <2>5 DEF SimpleGraphs
    <3>3. SUFFICES ASSUME NEW n \in Connected
                   PROVE  Cardinality({e \in G : n \in e}) < Cardinality(Connected)
      BY <3>1, <3>3 DEF Degree
    <3> DEFINE  nEdges == {e \in G : n \in e}
                PossibleNEdges == {{m, n} : m \in Connected \ {n}}
    <3>4. /\ Cardinality(nEdges) \in Nat
          /\ Cardinality(nEdges) \leq Cardinality(PossibleNEdges)
      (* FS_Image is a lemma scheme, thus this PO is second-order! *)
      (*BY Zipper, <3>2, FS_Subset, FS_CardinalityType, FS_Image,
         UseWith, With(Connected \ {n}), With(PossibleNEdges)*)
      <4>1. IsFiniteSet(Connected \ {n})
        BY FS_Subset
      <4>2. IsFiniteSet(PossibleNEdges)
        BY <4>1, FS_Image, Isa
      <4>3. nEdges \in SUBSET PossibleNEdges
        (*BY <3>2*)
        <5>1 SUFFICES ASSUME NEW e \in nEdges
                      PROVE \E m \in Connected \ {n} : e = {m, n}
            (* FIXME I don't know why Zipper fails here *)
            OBVIOUS
        <5> QED
            BY <3>2
      <4>. QED
        (*BY <4>2, <3>2, FS_Subset, FS_CardinalityType*)
        BY <4>2, <4>3, <3>2, FS_Subset, FS_CardinalityType
    <3> DEFINE NC == Cardinality(Connected \ {n})
    <3>5. /\ IsFiniteSet(Connected \ {n})
          /\ NC \in Nat
          /\ NC < Cardinality(Connected)
      (* TODO Investigate *)
      <4> \A m, p \in Int : m <= p /\ m # p => m < p OBVIOUS
      <4> Nat \subseteq Int OBVIOUS
      <4>1 Connected \ {n} \in SUBSET Connected
        OBVIOUS
      <4>2 /\ IsFiniteSet(Connected \ {n})
           /\ Cardinality(Connected \ {n}) <= Cardinality(Connected)
        BY <2>2, FS_Subset
      <4>3 Cardinality(Connected \ {n}) \in Nat
        BY <4>2, FS_CardinalityType
      <4>4 Cardinality(Connected \ {n}) < Cardinality(Connected)
        (* FIXME Zipper with longer timeout *)
        (* Would be nice if <4>1 wasn't necessary. *)
        BY ZipperT(10), <2>2, <4>1, <4>2, <4>3, FS_Subset
      <4> QED
        BY <4>2, <4>3, <4>4
    <3>. DEFINE f == [m \in Connected \ {n} |-> {m,n}]
    <3>6. f \in Bijection(Connected \ {n}, PossibleNEdges)
      BY Fun_IsBij, Zenon
    <3>7. NC = Cardinality(PossibleNEdges)
      BY <3>5, <3>6, FS_Bijection DEF ExistsBijection
    <3>. QED  BY <2>2, <3>4, <3>5, <3>7
      (* TODO Investigate *)
  <2>7. DEFINE f == [n \in Connected |-> Degree(n, G)]
  <2>8. f \in [Connected -> 1 .. (Cardinality(Connected)-1)]
    (*BY <2>6, <2>2*)
    <3> \A m, n \in Int :
            \A p : p \in m..n <=> p \in Int /\ m <= p /\ p <= n
            OBVIOUS (* TODO Implement (how did I miss this one?) *)
    <3> \A m, n \in Int : m < n <=> m <= (n-1) OBVIOUS (* TODO Comparisons facts *)
    <3> \A m, n \in Int : m-n \in Int OBVIOUS
    <3> \A m, n : m <= n <=> n >= m OBVIOUS (* TODO *)
    <3> \A m \in Nat : m # 0 => m >= 1 OBVIOUS (* TODO *)
    <3> \A n : n \in Nat => n \in Int OBVIOUS (* TODO Make an axiom *)
    <3> 1 \in Nat OBVIOUS (* TODO Make an axiom *)
    <3>1 DOMAIN f = Connected OBVIOUS
    <3> HIDE DEF Connected
    <3> SUFFICES ASSUME NEW n \in Connected
                 PROVE Degree(n, G) \in 1..(Cardinality(Connected)-1)
        (* FIXME Zipper succeeds if Connected is opaque *)
        BY <3>1 DEF Connected
    <3> USE DEF Connected
    <3>2 Degree(n, G) \in Nat BY <2>6
    <3>3 Degree(n, G) >= 1 BY <2>6
    <3>4 Degree(n, G) < Cardinality(Connected) BY <2>6
    <3>5 Cardinality(Connected) \in Nat BY <2>2
    <3> QED BY <3>2, <3>3, <3>4, <3>5
  <2>9. \E m, n \in Connected: m # n /\ f[m] = f[n]
    (*BY <2>2, <2>4, <2>8, FS_Interval, FS_PigeonHole*)
    <3> DEFINE CC1 == Cardinality(Connected)-1
    <3>1. /\ IsFiniteSet(1 .. CC1)
          /\ Cardinality(1 .. CC1) < Cardinality(Connected)
      (*BY <2>2, <2>4, FS_Interval*)
      <4> \A m, n \in Int : m-n \in Int OBVIOUS (* TODO Artihmetic fact *)
      <4> \A m, n \in Int : m >= (n+1) <=> n < m OBVIOUS (* TODO *)
      <4> \A m \in Int : m-1 < m OBVIOUS (* TODO *)
      <4> \A n \in Int : n - 1 + 1 = n OBVIOUS (* TODO *)
      <4> 1 = 0+1 OBVIOUS (* TODO *)
      <4> \A n : n \in Nat <=> n \in Int /\ 0 <= n OBVIOUS (* TODO Implement axiom *)
      <4> 1 \in Int OBVIOUS (* TODO Implement axiom *)
      <4> 0 \in Int OBVIOUS (* TODO Implement axiom *)
      (* Zipper is able to solve this problem with the axioms above
         and a longer timeout.  See below for the source of the problem. *)
      (*<4> QED
        BY ZipperT(15), <2>2, <2>4, FS_Interval*)
      <4>1 IsFiniteSet(1 .. CC1)
        BY FS_Interval, <2>2
      <4> SUFFICES Cardinality(1 .. CC1) < Cardinality(Connected)
        BY <4>1
      <4> HIDE DEF Connected
      <4>2 CASE 1 > CC1
        BY FS_Interval, <2>2, <2>4, <4>2
      <4>3 CASE ~ (1 > CC1)
        (*BY ZipperT(15), FS_Interval, <2>2, <2>4, <4>3*)
        <5> Cardinality(1 .. CC1) = CC1 - 1 + 1
          (* FIXME Zipper with longer timeout *)
          BY ZipperT(10), FS_Interval, <2>2, <2>4, <4>3
        <5> QED
          BY <2>2
      <4> QED
        BY <4>2, <4>3
    <3> QED  BY <2>2, <2>4, <2>8, <3>1, FS_PigeonHole, Isa
  <2>. QED  BY <1>1, <1>3, <2>9
<1>. QED  BY <1>2, <1>3
=============================================================================
