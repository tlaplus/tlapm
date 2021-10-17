------------------------- MODULE FiniteSetTheoremsLL -----------------------
(***************************************************************************)
(*                                                                         *)
(* This is a first pass at a library module for reasoning about            *)
(* IsFiniteSet and Cardinality.  Here are some reamrks about what I've     *)
(* done:                                                                   *)
(*                                                                         *)
(*  - I proved a few rules that were trivial consequences of others, but   *)
(*    I didn't check any of the rules with TLC so there are undoubtedly    *)
(*    mistakes.                                                            *)
(*                                                                         *)
(*  - I gave no thought to names, so none of the theorem names should be   *)
(*    taken seriously.                                                     *)
(*                                                                         *)
(*  - I combined related rules about IsFiniteSet and Cardinality into      *)
(*    single theorems instead of keeping them separate.  I don't know      *)
(*    it that's a good idea.                                               *)
(*                                                                         *)
(*  - I scanned through the Isabelle library but probably missed some      *)
(*    important rules.  I did deliberately leave out quite a few rules     *)
(*    that seemed to be easy consequences of other rules.  But I'm not     *)
(*    sure where the right balance is between providing potentially        *)
(*    useful rules and keeping the list of rules small enough so the       *)
(*    user can find what she's looking for.                                *)
(*                                                                         *)
(*  - I didn't include any rules corresponding to the Isabelle "folding"   *)
(*    rules.  I suspect they're not very useful for us.  For example,      *)
(*    I think that while one often wants to sum a sequence of integers,    *)
(*    it's rare to want to sum a set of integers.  But I could very        *)
(*    well be wrong about that.                                            *)
(***************************************************************************)

(***************************************************************************)
(* The standard modules use LOCAL INSTANCE statements instead of EXTENDS   *)
(* to keep from exporting other standard modules.  I didn't do that        *)
(* because I don't know if the prover can cope with that.  For example, if *)
(* this module were to import the Integers module with                     *)
(*                                                                         *)
(*   LOCAL INSTANCE Integers                                               *)
(*                                                                         *)
(* I don't know if the prover would know that the + in these theorems is   *)
(* the same plus as the one from Integers when the user writes             *)
(*                                                                         *)
(*   EXTENDS Integers, FiniteSetTheorems                                   *)
(***************************************************************************)
EXTENDS FiniteSets, Integers, TLAPS

THEOREM EmptySetFinite == IsFiniteSet({}) /\ Cardinality({}) = 0

(**
  split the following theorems in two parts since the first part doesn't
  need the hypothesis about x (not) being in S

THEOREM AddElementToFiniteSet ==
         \A S, x : IsFiniteSet(S) /\ x \notin S =>
            /\ IsFiniteSet(S \cup {x})
            /\ Cardinality(S \cup {x}) = Cardinality(S) + 1
 **)

THEOREM RemoveElementFromFiniteSet ==
          \A S, x : IsFiniteSet(S) /\ x \in S =>
            /\ IsFiniteSet(S \ {x})
            /\ Cardinality(S \ {x}) = Cardinality(S) - 1

THEOREM AddElementFiniteSet ==
  ASSUME NEW S, NEW x, IsFiniteSet(S)
  PROVE  IsFiniteSet(S \cup {x})

THEOREM AddElementCardinality ==
  ASSUME NEW S, NEW x,
         IsFiniteSet(S), x \notin S
  PROVE  Cardinality(S \cup {x}) = Cardinality(S) + 1

(***************************************************************************)
(* This is a trivial consequence of the above, but probably useful enough  *)
(* to include.                                                             *)
(***************************************************************************)
THEOREM SingletonSetFinite ==
          \A x : IsFiniteSet({x}) /\ (Cardinality({x}) = 1)
BY EmptySetFinite, AddElementFiniteSet, AddElementCardinality

THEOREM CardinalityType ==
          \A S : IsFiniteSet(S) => Cardinality(S) \in Nat

THEOREM FiniteSetInduction ==
    ASSUME NEW P(_),
           P({}),
           \A S, x : IsFiniteSet(S) /\ P(S) /\ x \notin S => P(S \cup {x})
    PROVE  \A S : IsFiniteSet(S) => P(S)

THEOREM GeneralFiniteSetInduction ==
    ASSUME NEW P(_),
           \A S : /\ IsFiniteSet(S)
                  /\ (\A T \in (SUBSET S) \ {S} : P(T)) => P(S)
    PROVE  \A S : IsFiniteSet(S) => P(S)

THEOREM SubsetInduction ==
    ASSUME NEW P(_), NEW U, IsFiniteSet(U),
           \A S \in SUBSET U :
              (\A T \in (SUBSET S) \ {S} : P(T)) => P(S)
    PROVE  P(U)

THEOREM SubsetOfFiniteSet ==
          \A S, T : IsFiniteSet(T) /\ (S \subseteq T) =>
                      /\ IsFiniteSet(S)
                      /\ Cardinality(S) \leq Cardinality(T)
                      /\ S = T <=> Cardinality(S) = Cardinality(T)

(***************************************************************************)
(* The following is in the Isabelle library but probably doesn't need to   *)
(* be on ours.                                                             *)
(***************************************************************************)
THEOREM  ASSUME NEW P(_, _), NEW S , \A x \in S : \E y : P(x, y)
         PROVE  LET f == [x \in S |-> CHOOSE y : P(x, y)]
                IN  \A x \in S : P(x, f[x])
OBVIOUS

(***************************************************************************)
(* I wonder if the following definitions should be in a separate module    *)
(* since other standard modules might need them.  However, it won't hurt   *)
(* to put them here for now and put them in a separate module later if     *)
(* necessary.                                                              *)
(***************************************************************************)
IsSurjectiveFunction(f, S, T) == /\ f \in [S -> T]
                           /\ \A t \in T : \E s \in S : f[s] = t

IsInjectiveFunction(f, S, T) == /\ f \in [S -> T]
                             /\ \A s1, s2 \in S : (s1 # s2) => (f[s1] # f[s2])

IsBijection(f, S, T) == /\ IsSurjectiveFunction(f, S, T)
                        /\ IsInjectiveFunction(f, S, T)

THEOREM CountingElements ==
         \A n \in Nat :
           \A S : IsFiniteSet(S) /\ (Cardinality(S) = n) <=>
             \E f : IsBijection(f, 1..n, S)

THEOREM IntervalCardinality ==
           \A i, j \in Int : i =< j => /\ IsFiniteSet(i..j)
                                       /\ Cardinality(i..j) = j - i + 1
  <1> SUFFICES ASSUME NEW i \in Int, NEW j \in Int,
                      i =< j
               PROVE  Cardinality(i..j) = j - i + 1
    OBVIOUS
  <1> DEFINE f == [x \in 1..(j-i+1) |-> x + i - 1]
  <1>1. f \in [1..(j-i+1) -> i..j]
    BY SMT
  <1>2. IsBijection(f, 1..(j-i+1), i..j)
    <2>1. \A s1, s2 \in 1..(j-i+1) : (s1 # s2) => (f[s1] # f[s2])
      BY SMT
    <2>2. \A t \in i..j : \E s \in 1..(j-i+1) : f[s] = t
      BY SMT
    <2>3. QED
     BY <1>1, <2>1, <2>2 DEF IsBijection, IsInjectiveFunction, IsSurjectiveFunction \* SMT doesn't prove this.
  <1>3. QED
    BY <1>1, <1>2, CountingElements, SMT

(***************************************************************************)
(* I'm not sure if we need this, since its proof is so simple.             *)
(***************************************************************************)
THEOREM BoundedSetOfNaturalsFinite ==
           \A S \in SUBSET Nat, n \in Nat :
             (\A s \in S : n \geq s) =>
                 /\ IsFiniteSet(S)
                 /\ Cardinality(S) \leq n+1
  <1> SUFFICES ASSUME NEW S \in SUBSET Nat, NEW n \in Nat,
                      \A s \in S : n \geq s
               PROVE  /\ IsFiniteSet(S)
                      /\ Cardinality(S) \leq n+1
    OBVIOUS
  <1>1. S \subseteq 0..n
    BY SMT
  <1>2. /\ IsFiniteSet(0..n)
        /\ Cardinality(0..n) = n+1
    BY <1>1, IntervalCardinality, SMT
  <1>3. QED
    BY <1>1, <1>2, SubsetOfFiniteSet  \* SMT fails on this

THEOREM UnionOfFiniteSets ==
         \A S, T : IsFiniteSet(S) /\ IsFiniteSet(T) =>
              /\ IsFiniteSet(S \cup T)
              /\ Cardinality(S \cup T) =
                   Cardinality(S) + Cardinality(T) - Cardinality(S \cap T)

THEOREM UNIONofFiniteSets ==
          \A S : /\ IsFiniteSet(S)
                 /\ \A T \in S : IsFiniteSet(T)
                 => IsFiniteSet(UNION S)

(***************************************************************************)
(* I don't know how to generalize this simply enough to handle the         *)
(* Cartesian product of n sets.                                            *)
(***************************************************************************)
THEOREM ProductOfFiniteSets ==
          \A S, T : IsFiniteSet(S) /\ IsFiniteSet(T) =>
                      /\ IsFiniteSet(S \X T)
                      /\ Cardinality(S \X T) = Cardinality(S) * Cardinality(T)


THEOREM DifferenceOfFiniteSets ==
          \A S, T : IsFiniteSet(S) =>
                      /\ IsFiniteSet(S \ T)
                      /\ IsFiniteSet(S \cap T)
                      /\ Cardinality(S \ T) = Cardinality(S) - Cardinality(S \cap T)

THEOREM ImageOfFiniteSet ==
          \A f, S, T : IsSurjectiveFunction(f, S, T) /\ IsFiniteSet(S) =>
                         /\ IsFiniteSet(T)
                         /\ Cardinality(T) \leq Cardinality(S)

THEOREM BijectionOfFiniteSet ==
         \A f, S, T : IsBijection(f, S, T) /\ IsFiniteSet(S) =>
                        /\ IsFiniteSet(T)
                        /\ Cardinality(S) = Cardinality(T)

THEOREM ReverseBijectionOfFiniteSet ==
          \A f, S, T : IsBijection(f, S, T) /\ IsFiniteSet(T) =>
                        /\ IsFiniteSet(S)
                        /\ Cardinality(S) = Cardinality(T)

 =============================================================================
\* Modification History
\* Last modified Wed Jun 26 14:50:32 CEST 2013 by merz
\* Last modified Wed Jun 26 14:13:04 CEST 2013 by merz
\* Last modified Wed Jun 12 08:15:37 PDT 2013 by lamport
\* Last modified Wed Jun 12 08:00:09 PDT 2013 by lamport
\* Last modified Fri Mar 15 11:52:30 CET 2013 by merz
\* Created Thu Mar 07 14:34:00 PST 2013 by lamport
