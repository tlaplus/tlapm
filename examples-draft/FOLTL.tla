------------------------------- MODULE FOLTL --------------------------------
(***************************************************************************)
(* Experiments with proofs about first-order temporal logic.               *)
(***************************************************************************)
EXTENDS Integers, FiniteSetTheorems, WellFoundedInduction, TLAPS

(***************************************************************************)
(* The following theorem has a temporal flavor but in fact A(_) is         *)
(* declared as a constant, and the proof obligation passed to the          *)
(* backend provers is a simple tautology.                                  *)
(***************************************************************************)
THEOREM ASSUME NEW A(_), NEW S
        PROVE  (\A x \in S : []A(x)) <=> [](\A x \in S : A(x))
OBVIOUS

(***************************************************************************)
(* The analogous theorem for a temporal formula A(_) is also proved        *)
(* automatically because the coalescing algorithm knows that universal     *)
(* quantification commutes with [].                                        *)
(***************************************************************************)
THEOREM ASSUME TEMPORAL A(_), NEW S
        PROVE  (\A x \in S : []A(x)) <=> [](\A x \in S : A(x))
OBVIOUS

(***************************************************************************)
(* As a concrete example of the above, we can prove the following theorem. *)
(***************************************************************************)
THEOREM ASSUME NEW n \in Nat, STATE x
        PROVE  (\A i \in 1..n : []<>(x=i)) <=> [](\A i \in 1..n : <>(x=i))
OBVIOUS

(***************************************************************************)
(* Attempting to prove the above theorem for a non-constant set S fails,   *)
(* as it should. However, the proof obligation sent to the backend provers *)
(* LOOKS WRONG because the universal quantifier on the right-hand side is  *)
(* moved out of the scope of the [] formula.                               *)
(***************************************************************************)
THEOREM ASSUME TEMPORAL A(_), STATE S
        PROVE  (\A x \in S : []A(x)) <=> [](\A x \in S : A(x))
OBVIOUS

-----------------------------------------------------------------------------

(***************************************************************************)
(* The following theorem asserts that quantification over a finite         *)
(* constant sets commutes with <>[]. (The axiom STL6 from the TLA paper    *)
(* asserts this for a conjunction of two formulas, hence the name of the   *)
(* theorem.) Note that finiteness is essential here.                       *)
(***************************************************************************)
THEOREM STL6_gen ==
  ASSUME NEW S, IsFiniteSet(S), TEMPORAL F(_)
  PROVE  (\A x \in S : <>[]F(x)) <=> <>[](\A x \in S : F(x))
<1>. DEFINE G(T) == (\A x \in T : <>[]F(x)) <=> <>[](\A x \in T : F(x))
<1>1. G({})
  <2>1. \A x \in {} : F(x)  OBVIOUS
  <2>2. <>[](\A x \in {} : F(x))  BY <2>1, PTL
  <2>. QED  BY <2>2
<1>2. ASSUME NEW T, NEW z
      PROVE  G(T) => G(T \cup {z})
  <2>1. (\A x \in T \cup {z} : <>[]F(x)) <=> <>[]F(z) /\ (\A x \in T : <>[]F(x))
    \* OBVIOUS fails due to coalescing problem
    <3>. DEFINE FF(x) == <>[]F(x)
    <3>. HIDE DEF FF
    <3>. (\A x \in T \cup {z} : FF(x)) <=> FF(z) /\ (\A x \in T : FF(x))
      OBVIOUS
    <3>. QED  BY DEF FF
  <2>2. <>[]F(z) /\ <>[](\A x \in T : F(x)) <=> <>[](F(z) /\ \A x \in T : F(x))
    BY PTL  \* instance of STL6
  <2>3. <>[](F(z) /\ \A x \in T : F(x)) <=> <>[](\A x \in T \cup {z} : F(x))
    <3>1. (F(z) /\ \A x \in T : F(x)) <=> (\A x \in T \cup {z} : F(x))
      OBVIOUS
    <3>. QED  BY <3>1, PTL
  <2>. QED  BY <2>1, <2>2, <2>3
<1>. QED
  <2>. HIDE DEF G
  <2>1. ASSUME NEW T, IsFiniteSet(T)  PROVE G(T)
    BY <1>1, <1>2, IsFiniteSet(T), FS_Induction, IsaM("blast")
  <2>2.G(S) BY <2>1  \* why does the proof fail without this step?
  <2>. QED  BY <2>2 DEF G

-----------------------------------------------------------------------------

(***************************************************************************)
(* The LATTICE rule from the TLA paper underlies liveness proofs based     *)
(* on well-founded orderings.                                              *)
(***************************************************************************)
THEOREM LATTICE ==
  ASSUME NEW R, NEW S, IsWellFoundedOn(R,S), TEMPORAL F(_), TEMPORAL G
         (* the following is not recognized as a [] formula, and we
            have to move it into the conclusion and write the theorem as
            as implication in order to be able to use the PTL backend
            \A x \in S : F(x) ~> (G \/ \E y \in SetLessThan(x,R,S) : F(y))
         *)
  PROVE  (\A x \in S : F(x) ~> (G \/ \E y \in SetLessThan(x,R,S) : F(y)))
         => \A x \in S : F(x) ~> G
<1>. DEFINE H(x) == F(x) ~> G
            LT(x) == F(x) ~> (G \/ \E y \in SetLessThan(x,R,S) : F(y))
<1>1. ASSUME NEW z \in S
      PROVE  (\A x \in S : LT(x))
             => ((\A y \in SetLessThan(z,R,S) : H(y)) => H(z))
  <2>0. (\A x \in S : LT(x)) => LT(z)
    <3>. HIDE DEF LT  \* necessary due to coalescing problem
    <3>. QED  OBVIOUS
  <2>1. (\A y \in SetLessThan(z,R,S) : F(y) => <>G) 
        <=> ((\E y \in SetLessThan(z,R,S) : F(y)) => <>G)
    OBVIOUS
  <2>2. [](\A y \in SetLessThan(z,R,S) : F(y) => <>G) 
        <=> []((\E y \in SetLessThan(z,R,S) : F(y)) => <>G)
    BY <2>1, PTL
  \* cannot write "H(y)" on the left-hand side because the PM doesn't 
  \* expand "F(y) ~> G" to "[](F(y) => <>G)" 
  <2>3. (\A y \in SetLessThan(z,R,S) : [](F(y) => <>G))
        <=> [](\A y \in SetLessThan(z,R,S) : F(y) => <>G)
    OBVIOUS
  <2>. QED  BY <2>0, <2>2, <2>3, PTL
<1>2. QED
  <2>. HIDE DEF H
  <2>. (\A x \in S : LT(x)) => \A x \in S: H(x)
    BY <1>1, WFInduction, IsaM("blast")
  <2>. QED  BY DEF H

=============================================================================
\* Modification History
\* Last modified Sat Nov 16 08:41:21 CET 2019 by merz
\* Last modified Tue Nov 05 18:40:17 CET 2019 by merz
\* Last modified Tue Nov 05 05:30:04 PST 2019 by lamport
\* Created Wed Mar 15 11:46:27 PDT 2017 by lamport
