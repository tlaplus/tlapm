---------------------- MODULE NaturalsInduction_test ------------------------
(***************************************************************************)
(* This module contains useful theorems for inductive proofs and recursive *)
(* definitions over the naturals.                                          *)
(*                                                                         *)
(* Some of the statements of the theorems are decomposed in terms of       *)
(* definitions.  This is done for two reasons:                             *)
(*                                                                         *)
(*  - It makes it easier for the backends to instantiate the theorems      *)
(*    when those definitions are not expanded.                             *)
(*                                                                         *)
(*  - It can be convenient when writing proofs to use those definitions    *)
(*    rather than having to write out their expansions.                    *)
(***************************************************************************)
EXTENDS Integers, TLAPS

(***************************************************************************)
(* The following is the simple statement of inductions over the naturals.  *)
(* For predicates P defined by a moderately complex operator, it is often  *)
(* useful to hide the operator definition before using this theorem. That  *)
(* is, you first define a suitable operator P (not necessarily by that     *)
(* name), prove the two hypotheses of the theorem, and then hide the       *) 
(* definition of P when using the theorem.                                 *)
(***************************************************************************)
THEOREM NatInduction == 
  ASSUME NEW P(_),
         P(0),
         \A n \in Nat : P(n) => P(n+1)
  PROVE  \A n \in Nat : P(n)
BY IsaM("(intro natInduct, auto)")

(***************************************************************************)
(* A useful corollary of NatInduction                                      *)
(***************************************************************************)
THEOREM DownwardNatInduction == 
  ASSUME NEW P(_), NEW m \in Nat, P(m),
         \A n \in 1 .. m : P(n) => P(n-1)
  PROVE  P(0)
<1>. DEFINE Q(i) == i \leq m => P(m-i)
<1>1. Q(0)  OBVIOUS
<1>2. ASSUME NEW n \in Nat, Q(n)
      PROVE  Q(n+1)
  BY <1>2
<1>3. \A n \in Nat : Q(n)  BY <1>1, <1>2, NatInduction, Isa
<1>. QED  BY <1>3, Isa

(***************************************************************************)
(* The following theorem expresses a stronger induction principle,         *)
(* also known as course-of-values induction, where the induction           *)
(* hypothesis is available for all strictly smaller natural numbers.       *)
(***************************************************************************)
THEOREM GeneralNatInduction ==
          ASSUME NEW P(_),
                 \A n \in Nat : (\A m \in 0..(n-1) : P(m)) => P(n)
          PROVE  \A n \in Nat : P(n)
<1> DEFINE Q(n) == \A m \in 0..n : P(m)
<1>1. Q(0) BY SMT
<1>2. \A n \in Nat : Q(n) => Q(n+1)  BY SMT
<1>3. \A n \in Nat : Q(n)  BY <1>1, <1>2, NatInduction, Isa
<1>4. QED BY ONLY <1>3, SMT

(***************************************************************************)
(* The following theorem says that a recursively defined function f over   *)
(* the natural numbers is well-defined if for every n \in Nat the          *)
(* definition of f[n] depends only on arguments smaller than n.            *)
(***************************************************************************)
THEOREM RecursiveFcnOfNat ==
  ASSUME NEW Def(_,_), 
         ASSUME NEW n \in Nat, NEW g, NEW h,
                \A i \in 0..(n-1) : g[i] = h[i] 
         PROVE  Def(g, n) = Def(h, n)
  PROVE  LET f[n \in Nat] == Def(f, n)
         IN  f = [n \in Nat |-> Def(f, n)]
<1>. SUFFICES \E ff : ff = [n \in Nat |-> Def(ff, n)]
  OBVIOUS
  (*************************************************************************)
  (* The strategy of the proof is to define a sequence F of approximations *)
  (* such that F[n] is a function with domain 0 .. n-1 that computes       *)
  (* F[n][i] by applying the definition to the preceding approximation     *)
  (* function F[n-1].                                                      *)
  (*************************************************************************)
<1>. DEFINE F[n \in Nat] == [i \in 0 .. n-1 |-> Def(F[n-1], i)]
            f[n \in Nat] == F[n+1][n]

  (*************************************************************************)
  (* We first show that F itself is well-defined by diagonalization        *)
  (* over functions that are defined over finite intervals of integers.    *)
  (*************************************************************************)
<1>1. F = [n \in Nat |-> [i \in 0 .. n-1 |-> Def(F[n-1], i)]]
  <2>. SUFFICES \E FF : FF = [n \in Nat |-> [i \in 0 .. n-1 |-> Def(FF[n-1], i)]]
    OBVIOUS
  <2>. DEFINE P(g,k) == g = [n \in 0 .. k |-> [i \in 0 .. n-1 |-> Def(g[n-1], i)]]
              G(k) == CHOOSE g : P(g,k)
              FF == [n \in Nat |-> [i \in 0 .. n-1 |-> G(n)[n][i] ]]
  <2>0. ASSUME NEW g, NEW k \in Nat, P(g,k),
               NEW n \in 0 .. k, NEW i \in 0 .. n-1
        PROVE  g[n][i] = Def(g[n-1], i)
    <3>. DEFINE gg == [m \in 0 .. k |-> [j \in 0 .. m-1 |-> Def(g[m-1], j)]]
    <3>1. gg[n][i] = Def(g[n-1],i)  OBVIOUS
    <3>2. g = gg  BY <2>0, Zenon
    <3>. QED  BY <3>1, <3>2, Zenon
  <2>1. \A k \in Nat : \E g : P(g,k)
    <3>. DEFINE Q(k) == \E g : P(g,k)
    <3>. SUFFICES \A k \in Nat : Q(k)  OBVIOUS
    <3>1. Q(0)
      <4>. DEFINE g0 == [n \in {0} |-> [i \in {} |-> {}]]
      <4>1. P(g0, 0)  OBVIOUS
      <4>. QED  BY <4>1
    <3>2. ASSUME NEW k \in Nat, Q(k)
          PROVE  Q(k+1)
      <4>1. PICK g : P(g,k)  BY <3>2
      <4>1a. ASSUME NEW n \in 0 .. k, NEW i \in 0 .. n-1
             PROVE  g[n][i] = Def(g[n-1], i)
        BY <4>1, <2>0
      <4>. DEFINE h == [n \in 0 .. k+1 |-> [i \in 0 .. n-1 |-> Def(g[n-1], i) ]]
      <4>2. h = [n \in 0 .. k+1 |-> [i \in 0 .. n-1 |-> Def(h[n-1], i)]]
        <5>. SUFFICES ASSUME NEW n \in 0 .. k+1, NEW i \in 0 .. n-1
                      PROVE  h[n][i] = Def(h[n-1], i)
          BY Zenon
        <5>1. h[n][i] = Def(g[n-1], i)  OBVIOUS
        <5>2. ASSUME NEW j \in 0 .. i-1
              PROVE  g[n-1][j] = h[n-1][j]
          BY <4>1a
        <5>. HIDE DEF h
        <5>3. Def(g[n-1],i) = Def(h[n-1],i)  BY <5>2
        <5>. QED  BY <5>1, <5>3
      <4>. HIDE DEF h
      <4>. QED  BY <4>2
    <3>. HIDE DEF Q
    <3>. QED  BY <3>1, <3>2, NatInduction, Blast
  <2>2. \A k \in Nat : P(G(k), k)  BY <2>1
  <2>3. \A k \in Nat : \A l \in 0 .. k : \A i \in 0 .. l-1 : \A g,h : 
           P(g,k) /\ P(h,l) => g[l][i] = h[l][i]
    <3>. DEFINE Q(k) == \A l \in 0 .. k : \A i \in 0 .. l-1 : \A g,h : 
                           P(g,k) /\ P(h,l) => g[l][i] = h[l][i]
    <3>. SUFFICES \A k \in Nat : Q(k)  OBVIOUS
    <3>0. Q(0)  OBVIOUS
    <3>1. ASSUME NEW k \in Nat, Q(k)
          PROVE  Q(k+1)
      <4>. HIDE DEF P
      <4>. SUFFICES ASSUME NEW l \in 0 .. k+1, NEW i \in 0 .. l-1, NEW g, NEW h,
                           P(g,k+1), P(h,l)
                    PROVE  g[l][i] = h[l][i]
        OBVIOUS
      <4>1. /\ g[l][i] = Def(g[l-1],i)
            /\ h[l][i] = Def(h[l-1],i)
        BY <2>0
      <4>. DEFINE gg == [nn \in 0 .. k |-> [ii \in 0 .. nn-1 |-> Def(g[nn-1],ii)]]
                  hh == [nn \in 0 .. l-1 |-> [ii \in 0 .. nn-1 |-> Def(h[nn-1],ii)]]
      <4>2. P(gg,k)
        <5>1. ASSUME NEW nn \in 0 .. k, NEW j \in 0 .. nn-1
              PROVE  gg[nn-1] = g[nn-1]
          <6>. /\ nn-1 \in 0 .. k
               /\ nn-1 \in 0 .. k+1
            OBVIOUS
          <6>1. gg[nn-1] = [ii \in 0 .. nn-2 |-> Def(g[nn-2],ii)]  OBVIOUS
          <6>2. g[nn-1] = [ii \in 0 .. (nn-1)-1 |-> Def(g[(nn-1)-1],ii)]  BY DEF P
          <6>. QED  BY <6>1, <6>2
        <5>. QED  BY <5>1 DEF P
      <4>3. P(hh,l-1)
        <5>1. ASSUME NEW nn \in 0 .. l-1, NEW j \in 0 .. nn-1
              PROVE  hh[nn-1] = h[nn-1]
          <6>. /\ nn-1 \in 0 .. l-1
               /\ nn-1 \in 0 .. l
            OBVIOUS
          <6>1. hh[nn-1] = [ii \in 0 .. nn-2 |-> Def(h[nn-2],ii)]  OBVIOUS
          <6>2. h[nn-1] = [ii \in 0 .. (nn-1)-1 |-> Def(h[(nn-1)-1],ii)]  BY DEF P
          <6>. QED  BY <6>1, <6>2
        <5>. QED  BY <5>1 DEF P
      <4>4. \A m \in 0 .. i-1 : gg[l-1][m] = hh[l-1][m]  BY <3>1, <4>2, <4>3
      <4>5. \A m \in 0 .. i-1 : g[l-1][m] = gg[l-1][m]   BY <2>0
      <4>6. \A m \in 0 .. i-1 : h[l-1][m] = hh[l-1][m]   BY <2>0
      <4>7. \A m \in 0 .. i-1 : g[l-1][m] = h[l-1][m]    BY <4>4, <4>5, <4>6
      <4>8. Def(g[l-1],i) = Def(h[l-1],i)                BY <4>7
      <4>. QED  BY <4>8, <2>0
    <3>. HIDE DEF Q
    <3>. QED  BY <3>0, <3>1, NatInduction, Blast
  <2>4. FF = [n \in Nat |-> [i \in 0 .. n-1 |-> Def(FF[n-1], i)]]
    <3>. HIDE DEF G
    <3>. SUFFICES ASSUME NEW k \in Nat, NEW i \in 0 .. k-1
                  PROVE  FF[k][i] = Def(FF[k-1], i)
      OBVIOUS
    <3>1. FF[k][i] = G(k)[k][i]  OBVIOUS
    <3>2. G(k)[k][i] = Def(G(k)[k-1], i)  BY <2>2
    <3>. HIDE DEF P
    <3>3. \A j \in 0 .. i-1 : G(k)[k-1][j] = FF[k-1][j]  BY <2>2, <2>3
    <3>. HIDE DEF FF
    <3>4. Def(G(k)[k-1], i) = Def(FF[k-1], i)  BY <3>3
    <3>. QED  BY <3>1, <3>2, <3>4
  <2>. QED  BY <2>4

<1>. HIDE DEF F  \* from now on, use step <1>1 rather than the definition

  (*************************************************************************)
  (* The following step is a trivial consequence of <1>1 but the backend   *)
  (* provers are currently unable to prove it directly.                    *)
  (*************************************************************************)
<1>2. ASSUME NEW n \in Nat, NEW i \in 0 .. n-1
       PROVE  F[n][i] = Def(F[n-1], i)
  <2>. DEFINE G == [m \in Nat |-> [j \in 0 .. m-1 |-> Def(F[m-1],j)]]
  <2>1. G[n][i] = Def(F[n-1],i)  OBVIOUS
  <2>2. F = G  BY <1>1, Zenon
  <2>. QED  BY <2>1, <2>2, Zenon

  (*************************************************************************)
  (* Any two approximations F[n] and F[m] agree for arguments where they   *)
  (* are both defined.                                                     *)
  (*************************************************************************)
<1>. DEFINE P(n) == \A m \in 0 .. n : \A i \in 0 .. m-1 : F[n][i] = F[m][i]
<1>3. \A n \in Nat : P(n)
  <2>1. ASSUME NEW n \in Nat, \A k \in 0 .. n-1 : P(k)
        PROVE  P(n)
    <3>. SUFFICES ASSUME NEW m \in 0 .. n, NEW i \in 0 .. m-1
                  PROVE  F[n][i] = F[m][i]
      OBVIOUS
    <3>2. CASE m = n  BY <3>2
    <3>3. CASE n = 0  BY <3>3, SMT
    <3>4. CASE 0 < n /\ m \in 0 .. n-1
      <4>1. F[n][i] = Def(F[n-1],i)  BY <1>2
      <4>2. \A j \in 0 .. i-1 : F[n-1][j] = F[m-1][j]  BY <2>1, <3>4
      <4>3. Def(F[n-1],i) = Def(F[m-1],i)  BY <4>2
      <4>4. Def(F[m-1],i) = F[m][i]  BY <1>2
      <4>. QED  BY <4>1, <4>3, <4>4
    <3>. QED  BY <3>2, <3>3, <3>4, SMT
  <2>. HIDE DEF P
  <2>. QED  BY <2>1, GeneralNatInduction, Blast

  (*************************************************************************)
  (* The assertion follows immediately from the two preceding steps.       *)
  (*************************************************************************)
<1>4. f = [n \in Nat |-> Def(f,n)]
  <2>. SUFFICES ASSUME NEW n \in Nat
                PROVE  f[n] = Def(f,n)
    OBVIOUS
  <2>1. f[n] = Def(F[n], n)  BY <1>2
  <2>2. \A i \in 0 .. n-1 : F[n][i] = f[i]  BY <1>3
  <2>3. Def(F[n],n) = Def(f,n)  BY <2>2
  <2>. QED  BY <2>1, <2>3

<1>. QED  BY <1>4


(***************************************************************************)
(* The following theorem NatInductiveDef is what you use to justify a      *)
(* function defined by primitive recursion over the naturals.              *)
(***************************************************************************)
NatInductiveDefHypothesis(f, f0, Def(_,_)) == 
   (f =  CHOOSE g : g = [i \in Nat |-> IF i = 0 THEN f0 ELSE Def(g[i-1], i)])
NatInductiveDefConclusion(f, f0, Def(_,_)) ==
     f = [i \in Nat |-> IF i = 0 THEN f0 ELSE Def(f[i-1], i)]

THEOREM NatInductiveDef ==
  ASSUME NEW Def(_,_), NEW f, NEW f0,
         NatInductiveDefHypothesis(f, f0, Def)
  PROVE  NatInductiveDefConclusion(f, f0, Def)
<1>. DEFINE PRDef(g,n) == IF n = 0 THEN f0 ELSE Def(g[n-1], n)
            ff[n \in Nat] == PRDef(ff,n)
<1>1. ASSUME NEW n \in Nat, NEW g, NEW h,
             \A i \in 0 .. n-1 : g[i] = h[i]
      PROVE  PRDef(g,n) = PRDef(h,n)
  BY <1>1, Z3
<1>. HIDE DEF PRDef
<1>2. ff = [n \in Nat |-> PRDef(ff,n)]  BY <1>1, RecursiveFcnOfNat, Isa
<1>. USE DEF PRDef
<1>3. ff = f  BY DEF NatInductiveDefHypothesis
<1>. HIDE DEF ff
<1>. QED  BY <1>2, <1>3 DEF NatInductiveDefConclusion


(***************************************************************************)
(* The following two theorems allow you to prove the type of a recursively *)
(* defined function over the natural numbers.                              *)
(***************************************************************************)
THEOREM RecursiveFcnOfNatType ==
  ASSUME NEW f, NEW S, NEW Def(_,_), f = [n \in Nat |-> Def(f,n)],
         ASSUME NEW n \in Nat, NEW g, \A i \in 0 .. n-1 : g[i] \in S
         PROVE  Def(g,n) \in S
  PROVE  f \in [Nat -> S]
<1>1. SUFFICES \A n \in Nat : f[n] \in S
  OBVIOUS
<1>2. ASSUME NEW n \in Nat, \A i \in 0 .. n-1 : f[i] \in S
      PROVE  f[n] \in S
  BY <1>2, Zenon
<1>. QED  BY <1>2, GeneralNatInduction, Isa

THEOREM NatInductiveDefType ==
  ASSUME NEW Def(_,_), NEW S, NEW f, NEW f0 \in S,
         NatInductiveDefConclusion(f, f0, Def),
         f0 \in S,
         \A v \in S, n \in Nat \ {0} : Def(v, n) \in S
  PROVE  f \in [Nat -> S]
<1>. USE DEF NatInductiveDefConclusion
<1> SUFFICES \A n \in Nat : f[n] \in S
  OBVIOUS
<1>1. f[0] \in S  OBVIOUS
<1>2. ASSUME NEW n \in Nat, f[n] \in S
      PROVE  f[n+1] \in S
  <2>1. /\ n+1 \in Nat \ {0}
        /\ (n+1)-1 = n
   OBVIOUS
  <2>. QED  BY <2>1, <1>2
<1>. QED  BY <1>1, <1>2, NatInduction, Isa

(***************************************************************************)
(* The following theorems show uniqueness of functions recursively defined *)
(* over Nat.                                                               *)
(***************************************************************************)
THEOREM RecursiveFcnOfNatUnique ==
  ASSUME NEW Def(_,_), NEW f, NEW g,
         f = [n \in Nat |-> Def(f,n)],
         g = [n \in Nat |-> Def(g,n)],
         ASSUME NEW n \in Nat, NEW ff, NEW gg,
                \A i \in 0..(n-1) : ff[i] = gg[i] 
         PROVE  Def(ff, n) = Def(gg, n)
  PROVE  f = g
<1>1. SUFFICES \A n \in Nat : f[n] = g[n]
  OBVIOUS
<1>2. ASSUME NEW n \in Nat, \A i \in 0 .. n-1 : f[i] = g[i]
      PROVE  f[n] = g[n]
  <2>1. Def(f,n) = Def(g,n)  BY <1>2
  <2>. QED  BY <2>1, Zenon
<1>. QED
  BY <1>2, GeneralNatInduction, Isa

THEOREM NatInductiveUnique == 
  ASSUME NEW Def(_,_), NEW f, NEW g, NEW f0,
         NatInductiveDefConclusion(f, f0, Def),
         NatInductiveDefConclusion(g, f0, Def)
  PROVE  f = g
<1>. USE DEF NatInductiveDefConclusion
<1>1. SUFFICES \A n \in Nat : f[n] = g[n]
  OBVIOUS
<1>2. f[0] = g[0]  OBVIOUS
<1>3. ASSUME NEW n \in Nat, f[n] = g[n]
      PROVE  f[n+1] = g[n+1]
  <2>0. /\ n+1 \in Nat \ {0}
        /\ (n+1)-1 = n
    OBVIOUS
  <2>1. f[n+1] = Def(f[n], n+1)  BY <2>0
  <2>2. g[n+1] = Def(g[n], n+1)  BY <2>0
  <2>. QED  BY <2>1, <2>2, <1>3
<1>. QED
  BY <1>2, <1>3, NatInduction, Isa

=============================================================================
(***************************************************************************)
(* The following example shows how this module is used.                    *)
(***************************************************************************)

factorial[n \in Nat] == IF n = 0 THEN 1 ELSE n * factorial[n-1]

THEOREM FactorialDefConclusion == NatInductiveDefConclusion(factorial, 1, LAMBDA v,n : n*v)
<1>1. NatInductiveDefHypothesis(factorial, 1, LAMBDA v,n : n*v)
  BY DEF NatInductiveDefHypothesis, factorial 
<1>2. QED
  BY <1>1, NatInductiveDef

THEOREM FactorialDef == \A n \in Nat : factorial[n] = IF n = 0 THEN 1 ELSE n * factorial[n-1]
BY FactorialDefConclusion DEFS NatInductiveDefConclusion

THEOREM FactorialType == factorial \in [Nat -> Nat]
<1>1. \A v \in Nat, n \in Nat \ {0} : n * v \in Nat
  BY SMT
<1>2. QED
  BY <1>1, 1 \in Nat, NatInductiveDefType, FactorialDefConclusion, Auto


----------------------------------------------------------------------------
(* old stuff, probably no longer useful *)
(***************************************************************************)
(* To prove something about a recursively defined function f, you must     *)
(* first prove that it equals its definition.  The following theorem       *)
(* FiniteNatInductiveDef allows you to do that for recursively defined     *)
(* functions with domain 0..n for an integer n.  I don't know how useful   *)
(* that will be in practice, but it's needed as a lemma in proving the     *)
(* corresponding theorem about recursively defined functions with domain   *)
(* Nat.                                                                    *)
(***************************************************************************)
FiniteNatInductiveDefConclusion(f, f0, Def(_,_), n) ==
     f = [i \in 0..n |-> IF i = 0 THEN f0 ELSE Def(f[i-1], i)]
FiniteNatInductiveDefHypothesis(f, f0, Def(_,_), n) == 
   (f =  CHOOSE g : g = [i \in 0..n |-> IF i = 0 THEN f0 ELSE Def(g[i-1], i)])
                                       
THEOREM FiniteNatInductiveDef ==
          ASSUME NEW Def(_,_)
          PROVE  \A n \in Nat:
                   \A f, f0 :
                     FiniteNatInductiveDefHypothesis(f, f0, Def, n)
                     => FiniteNatInductiveDefConclusion(f, f0, Def, n)
<1> USE DEF FiniteNatInductiveDefHypothesis, FiniteNatInductiveDefConclusion
<1> DEFINE P(n) == \A f, f0 :
                     FiniteNatInductiveDefHypothesis(f, f0, Def, n)
                      => FiniteNatInductiveDefConclusion(f, f0, Def, n)
<1>1. P(0)
  <2> SUFFICES ASSUME NEW f, NEW f0,
                      P(0)!(f, f0)!1
               PROVE  P(0)!(f, f0)!2
    OBVIOUS
  <2> DEFINE g == [i \in 0..0 |-> f0]
  <2> g = [i \in 0..0 |-> IF i = 0 THEN f0 ELSE Def(g[i-1], i)]
    BY SMT
  <2> QED
    OBVIOUS

<1>2. ASSUME NEW n \in Nat, P(n)
      PROVE  P(n+1)
  <2>1. SUFFICES ASSUME NEW f, NEW f0,
                        P(n+1)!(f, f0)!1
                 PROVE  P(n+1)!(f, f0)!2
   BY <1>2
  <2> DEFINE h == CHOOSE g : g = [i \in 0..n |-> IF i = 0 THEN f0 
                                                          ELSE Def(g[i-1], i)]
  <2>2. h = [i \in 0..n |-> IF i = 0 THEN f0 ELSE Def(h[i-1], i)]
    BY <1>2, <2>1, Auto
  <2> DEFINE g == [i \in 0..(n+1) |-> IF i \in 0..n THEN h[i]
                                                    ELSE Def(h[i-1], i)]
  <2>3. g = [i \in 0..(n+1) |-> IF i = 0 THEN f0
                                         ELSE Def(g[i-1], i)]
    <3>. HIDE DEF h
    <3>1. SUFFICES ASSUME NEW i \in 0 .. n+1
                   PROVE  g[i] = IF i = 0 THEN f0 ELSE Def(g[i-1], i)
      OBVIOUS
    <3>2. CASE i = 0
      BY <2>2, <3>2, SMT
    <3>3. CASE i \in 0 .. n /\ i # 0
      <4>1. i-1 \in 0..n /\ i-1 \in 0 .. n+1
        BY <3>3, SMT
      <4>2. QED
        BY <2>2, <3>3, <4>1
    <3>4. CASE i = n+1
      BY <3>4, SMT
    <3>5. QED
      BY <3>2, <3>3, <3>4, SMT
  <2>4. QED
    BY <2>1, <2>2, <2>3
<1>3. QED
  BY <1>1, <1>2, NatInduction, Auto

(***************************************************************************)
(* The following theorem asserts that the CHOOSE implicit in a recursive   *)
(* definition of a function with domain 0..n has only one function to      *)
(* choose from.  I don't know if this is of any other use, but it's        *)
(* required as a lemma for proving the next theorem.                       *)
(***************************************************************************)
THEOREM FiniteNatInductiveUnique == 
          ASSUME NEW Def(_,_), NEW n \in Nat, NEW f, NEW h, NEW f0,
                 FiniteNatInductiveDefConclusion(f, f0, Def, n),
                 FiniteNatInductiveDefConclusion(h, f0, Def, n)
          PROVE  h = f
<1> DEFINE P(k) == \A ff, ff0, hh : 
                     FiniteNatInductiveDefConclusion(ff, ff0, Def, k)
                        /\ FiniteNatInductiveDefConclusion(hh, ff0, Def, k)
                     => (hh = ff)
<1>1. P(0)
  <2>1. 0..0 = {0}
    BY SMT
  <2>2. QED
    BY <2>1 DEF FiniteNatInductiveDefConclusion
    
<1>2. ASSUME NEW k \in Nat, P(k)
      PROVE  P(k+1)
  <2>1. SUFFICES ASSUME NEW ff, NEW ff0, NEW hh,
                        FiniteNatInductiveDefConclusion(ff, ff0, Def, k+1),
                        FiniteNatInductiveDefConclusion(hh, ff0, Def, k+1)
                 PROVE  hh = ff
    OBVIOUS
  <2> DEFINE Restrict(g) == [i \in 0..k |-> g[i]]
  <2>2. ASSUME NEW g, FiniteNatInductiveDefConclusion(g, ff0, Def, k+1)
        PROVE  FiniteNatInductiveDefConclusion(Restrict(g), ff0, Def, k)
    <3>1. SUFFICES \A i \in 0..k : Restrict(g)[i] = IF i = 0 THEN ff0 ELSE Def(Restrict(g)[i-1], i)
      BY DEF FiniteNatInductiveDefConclusion
    <3>2. \A i \in 0..(k+1) : g[i] = IF i = 0 THEN ff0 ELSE Def(g[i-1], i)
      BY <2>2 DEF FiniteNatInductiveDefConclusion
    <3>3. /\ 0..k \subseteq 0..(k+1)
          /\ \A i \in 0..(k+1) : (i # 0) => (i-1 \in 0..k)
      BY SMT
    <3> QED
      BY <3>2, <3>3
  <2>3. /\ FiniteNatInductiveDefConclusion(Restrict(ff), ff0, Def, k)
        /\ FiniteNatInductiveDefConclusion(Restrict(hh), ff0, Def, k)
    BY <2>1, <2>2
  <2>4. Restrict(ff) = Restrict(hh)
    BY <2>3, <1>2
  <2>5. SUFFICES \A i \in 0..(k+1) : ff[i] = hh[i]
    BY ONLY <2>1, <2>5 DEF FiniteNatInductiveDefConclusion
  <2>6. \A i \in 0..k : ff[i] = hh[i]
    BY <2>4
  <2>7. ff[k+1] = hh[k+1]
    <3>1. /\ k+1 # 0
          /\ (k+1)-1 \in 0..k
          /\ k+1 \in 0..(k+1)
          /\ (k+1)-1 = k
      BY SMT
    <3>2. QED
      BY ONLY <2>1, <2>6, <3>1 DEF FiniteNatInductiveDefConclusion
  <2>8. QED
    BY <2>6, <2>7, SMT

<1>. HIDE DEF P
<1>3. \A k \in Nat: P(k)
  BY <1>1, <1>2, NatInduction
<1>4. QED
  BY <1>3 DEF P

THEOREM NatInductiveDef ==
          ASSUME NEW Def(_,_), NEW f, NEW f0,
                 NatInductiveDefHypothesis(f, f0, Def)
          PROVE  NatInductiveDefConclusion(f, f0, Def)
<1> SUFFICES \E ff : ff = [i \in Nat |-> IF i = 0 THEN f0 ELSE Def(ff[i-1], i)]
 BY DEF NatInductiveDefHypothesis, NatInductiveDefConclusion
<1> DEFINE F(n) == CHOOSE g : g = [i \in 0..n |-> IF i = 0 THEN f0
                                                           ELSE Def(g[i-1], i)]
           ff[n \in Nat] == F(n)[n]
           P(n) == F(n)[n] = IF n = 0 THEN f0
                                      ELSE Def(ff[n-1], n)
<1>2. ASSUME NEW n \in Nat 
      PROVE  FiniteNatInductiveDefConclusion(F(n), f0, Def, n)
  BY FiniteNatInductiveDef, Auto DEF FiniteNatInductiveDefHypothesis
<1>3. \A n \in Nat : P(n)
  <2>1. P(0)
    <3>1. 0 \in 0..0
      BY SMT
    <3>2. QED 
      BY <1>2, <3>1, 0 \in Nat DEF FiniteNatInductiveDefConclusion
  <2>2. ASSUME NEW n \in Nat, P(n)
        PROVE  P(n+1)
    <3>1. F(n+1)[n] = F(n)[n]
      <4> DEFINE g == F(n)
                 h == F(n+1)
                 hh == [i \in 0..n |-> h[i]]
      <4>1. /\ FiniteNatInductiveDefConclusion(g, f0, Def, n)
            /\ FiniteNatInductiveDefConclusion(h, f0, Def, n+1)
        BY <1>2
      <4> HIDE DEF g, h
      <4>2. FiniteNatInductiveDefConclusion(hh, f0, Def, n)
        <5> SUFFICES ASSUME NEW i \in 0..n
                     PROVE  h[i] = IF i=0 THEN f0 ELSE Def(hh[i-1],i)
          BY DEF FiniteNatInductiveDefConclusion
        <5> /\ i \in 0..(n+1)
            /\ 0 \in 0..(n+1)
            /\ (i # 0) => i-1 \in 0..n
          BY SMT
        <5> QED
          BY <4>1 DEF FiniteNatInductiveDefConclusion
      <4>3. g = hh
        BY <4>1, <4>2, FiniteNatInductiveUnique
      <4>4. hh[n] = h[n]
        BY SMT
      <4>5. QED
        BY <4>3, <4>4 DEF g,h
    <3> HIDE DEF F
    <3>2. /\ n+1 \in Nat
          /\ n+1 \in 0..(n+1)
          /\ n+1 # 0
          /\ (n+1)-1 = n
      BY SMT
    <3>3. F(n+1)[n+1] = Def(F(n+1)[n], n+1)
     BY <1>2, <3>2 DEF FiniteNatInductiveDefConclusion 
    <3> QED
      BY <3>1, <3>3
  <2>3. QED
    BY <2>1, <2>2, NatInduction, Auto
<1> HIDE DEF F
<1>4. QED
  BY <1>3

=============================================================================
\* Modification History
\* Last modified Fri Feb 14 21:36:25 GMT-03:00 2014 by merz
\* Last modified Tue Oct 15 12:06:48 CEST 2013 by shaolin
\* Last modified Sat Nov 26 08:49:59 CET 2011 by merz
\* Last modified Mon Nov 07 08:58:05 PST 2011 by lamport
\* Created Mon Oct 31 02:52:05 PDT 2011 by lamport
