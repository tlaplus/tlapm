----------------------------- MODULE setEuclid_test -----------------------------
(***************************************************************************)
(* The ordinary Euclid algorithm computes the GCD (greatest common         *)
(* divisor) of two numbers M and N by using two variables x and y,         *)
(* initialized with x = M and y = N, and repeatedly subtracting the        *)
(* smaller of x and y from the larger until x and y are equal.  At that    *)
(* point, x and y both equal the GCD of M and N.                           *)
(*                                                                         *)
(* There is an obvious generalization that computes the GCD of a set of    *)
(* numbers.  Asked to write that algorithm, most programmers and computer  *)
(* scientists would use an array variable whose elements are initially     *)
(* equal to the given numbers.  The algorithm would subtract smaller       *)
(* elements from larger elements until all elements of the array are       *)
(* equal, at which point they all equal the GCD.  The code would probably  *)
(* use two nested loops looking for pairs of unequal array elements.       *)
(*                                                                         *)
(* However, I wrote that the generalization computes the GCD of a set of   *)
(* numbers, not an array of numbers.  The algorithm for computing the GCD  *)
(* of a set is much simpler and more elegant.  This module presents a      *)
(* PlusCal version of this algorithm.                                      *)
(***************************************************************************)

(***************************************************************************)
(* The following statement imports definitions from three standard         *)
(* modules.  The Integers module defines the usual arithmetic operations   *)
(* on integers, the set Nat of natural numbers, and the operator `..'      *)
(* where i..j is the set of integers from i through j.                     *)
(*                                                                         *)
(* The FiniteSets module defines the Cardinality operator and the operator *)
(* IsFiniteSet, where IsFiniteSet(S) is true iff S is a finite set.        *)
(*                                                                         *)
(* The TLAPS module defines some operators that are used when writing      *)
(* proofs to be checked by the TLAPS proof system.                         *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLAPS

(***************************************************************************)
(* We now declare Input, which is the set of numbers whose GCD we want to  *)
(* find.  We also declare the assumption that it is a finite, nonempty set *)
(* of positive integers--an assumption we name InputAssump for future      *)
(* reference.                                                              *)
(***************************************************************************)
CONSTANT Input

ASSUME InputAssump == /\ Input \subseteq Nat \ {0}
                      /\ Input # {}
                      /\ IsFiniteSet(Input)

(***************************************************************************
Here is the PlusCal algorithm, which as you can see appears inside a comment.
The `variables' statement declares S to be a variable with initial value
Input, and declares gcd to be a variable that will be given some
default initial value.  The algorithm sets gcd to be the GCD of Input when
it terminates.

--algorithm EuclidForSets {
    variables S = Input, gcd ;
    { lbl: while (Cardinality(S) > 1)
             { with (i \in S, j \in {s \in S : s > i})
                 {  S := (S \ {j}) \cup {j-i}
                 }
             } ;
           gcd := CHOOSE t \in S : TRUE
    }
}

In PlusCal, an execution step (an atomic action) consists of execution
from one lable to the next.  There is an implicit label Done at the end
of the algorithm.  Thus, each iteration of the while loop is one step,
and there is one final step that sets gcd.

The translator put TLA+ translation of this algorithm below, between the
BEGIN and END comments.  The translation adds a variable pc whose value
indicates the where in the algorithm the locus of control is.

The important parts of the specification are the initial predicate Init,
which specifies the initial state, and the next-state relation Next,
which describes how the state can change--unprimed variables referring
to their value in the old state and primed variables referring to their
value in the new state.  The second disjunction of Next allows steps that
leave the state unchanged when the algorithm has reached its terminating
state.  You can ignore that disjunction and those steps, which don't
affect invariance properties.
****************************************************************************)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES S, gcd, pc

vars == << S, gcd, pc >>

Init == (* Global variables *)
        /\ S = Input
        /\ gcd = defaultInitValue
        /\ pc = "lbl"

lbl == /\ pc = "lbl"
       /\ IF Cardinality(S) > 1
             THEN /\ \E i \in S:
                       \E j \in {s \in S : s > i}:
                         S' = ((S \ {j}) \cup {j-i})
                  /\ pc' = "lbl"
                  /\ gcd' = gcd
             ELSE /\ gcd' = (CHOOSE t \in S : TRUE)
                  /\ pc' = "Done"
                  /\ S' = S

Next == lbl
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* To assert and check the correctness of the algorithm, we must define    *)
(* the GCD of a set.  First, we define Max(T) to be the maximum of a       *)
(* finite set T of numbers.                                                *)
(***************************************************************************)
Max(T) == CHOOSE x \in T : \A y \in T : x >= y

(***************************************************************************)
(* Next, we define m | n to be true for positive integers m and n iff m    *)
(* divides n.  A simpler definition is                                     *)
(*                                                                         *)
(*    m | n == n % m = 0                                                   *)
(*                                                                         *)
(* but I prefer to define it without using the modulus operator % (defined *)
(* in the Integers module).                                                *)
(***************************************************************************)
m | n == \E q \in 1..n : n = q * m

(***************************************************************************)
(* We can now define GCD(T) to equal the GCD of a non-empty set of         *)
(* non-negative integers.  The obvious definition is                       *)
(*                                                                         *)
(*    GCD(T) == Max({d \in Nat \ {0} : \A t \in T : d | t})                *)
(*                                                                         *)
(* However, the TLC model checker can't evaluate this definition because   *)
(* it would have to try all elements d in Nat \ {0} in order to construct  *)
(* the set {d \in ...  }.  So, we use the following instead.               *)
(***************************************************************************)
GCD(T) == Max({d \in 1..Max(T) : \A t \in T : d | t})

(***************************************************************************)
(* We could check the correctness of the algorithm by adding the statement *)
(*                                                                         *)
(*    assert gcd = GCD(Input)                                              *)
(*                                                                         *)
(* after the assignment to gcd in the PlusCal code.  When running the      *)
(* model checker on a model that assigns a particular set of numbers to    *)
(* Inner, TLC will report an error if that assertion is not true when the  *)
(* `assert' statement is executed.                                         *)
(*                                                                         *)
(* Another way to check correctness is to observe from the translation     *)
(* that an execution of the algorithm has terminated iff pc = "Done",      *)
(* where pc is a variable, added by the translation, whose value indicates *)
(* where the locus of control is.  We can therefore check correctness by   *)
(* constructing a model that checks the invariance of the following        *)
(* formula                                                                 *)
(***************************************************************************)
CorrectTermination == (pc = "Done") => (gcd = GCD(Input))
-----------------------------------------------------------------------------
(***************************************************************************)
(* The Invariance Proof                                                    *)
(*                                                                         *)
(* We now prove that CorrectTermination is an invariant, meaning that it   *)
(* is true of all states of every behavior.  The standard way to prove     *)
(* this is to find an invariant Inv that satisfies the following three     *)
(* properties:                                                             *)
(*                                                                         *)
(*   1. Inv is true in any initial state.                                  *)
(*                                                                         *)
(*   2. Executing one step of the algorithm in any state satisfying Inv    *)
(*      yields a state satisfying Inv.                                     *)
(*                                                                         *)
(*   3. Any state satisfying Inv satisfies CorrectTermination              *)
(*                                                                         *)
(* By induction, 1 and 2 implies that Inv is an invariant (true in any     *)
(* state of any behavior).  Property 3 then implies that                   *)
(* CorrectTermination is an invariant.  An invariant satisfying 1 and 2 is *)
(* called an inductive invariant.                                          *)
(*                                                                         *)
(* Properties 1-3 are expressed in TLA+ by the following formulas:         *)
(*                                                                         *)
(*   1. Init => Inv                                                        *)
(*                                                                         *)
(*   2. Inv /\ Next => Inv'                                                *)
(*                                                                         *)
(*   3. Inv => CorrectTermination                                          *)
(*                                                                         *)
(* In property 2, the formula Inv' is obtained from Inv by replacing each  *)
(* variable v in Inv by v' (after completely expanding the definition of   *)
(* Inv).  Thus Inv' asserts that Inv is true in the next state.            *)
(*                                                                         *)
(* In an untyped logic like TLA+, the invariant Inv almost always asserts  *)
(* type correctness--meaning that the value of each variable is an element *)
(* of the proper set.  This is expressed by the following formula TypeOK.  *)
(* It asserts that S is a nonempty finite subset of positive integers and  *)
(* that pc equals either "lbl" or "Done".  Since the value of gcd is set   *)
(* only when the algorithm terminates, TypeOK asserts only that gcd is a   *)
(* positive integer when pc equals "Done".                                 *)
(***************************************************************************)
TypeOK == /\ /\ S \subseteq Nat \ {0}
             /\ S # {}
             /\ IsFiniteSet(S)
          /\ (pc = "Done") => (gcd \in Nat \ {0})
          /\ pc \in {"lbl", "Done"}

(***************************************************************************)
(* Here is the complete definition of the inductive invariant Inv.  It's   *)
(* most interesting part is the second conjunct.                           *)
(***************************************************************************)
Inv == /\ TypeOK
       /\ GCD(S) = GCD(Input)
       /\ CorrectTermination

(***************************************************************************)
(* Let's now prove properties 1-3.  We start with the easy ones,           *)
(* properties 1 and 3.  You should first convince yourself that they are   *)
(* obviously true.  (Writing out the proofs is a good exercise.)           *)
(***************************************************************************)
THEOREM Init => Inv
BY InputAssump DEF Init, Inv, TypeOK, CorrectTermination

THEOREM Inv => CorrectTermination
BY DEF Inv

(***************************************************************************)
(* We now come to the proof of property 2, which is always the hard part   *)
(* of an invariance.  I recommend that you now write an informal proof of  *)
(* this property.  You will probably prefer to reason about the PlusCal    *)
(* code rather than its the TLA+ translation.  You should observe that     *)
(* your proof requires the following two properties of the GCD.  Property  *)
(* GCD2 is obvious, but property GCD1 isn't.  Proving it is a nice little  *)
(* exercise.  However, this spec is meant to be an example of verifying an *)
(* algorithm, not of proving properties of numbers.  So, the proofs are    *)
(* omitted.                                                                *)
(***************************************************************************)
THEOREM GCD1 == \A T \in SUBSET (Nat \ {0}) :
                   IsFiniteSet(T) =>
                      \A x, y \in T : (x > y) => GCD(T) = GCD((T \ {x}) \cup {x-y})
PROOF OMITTED

THEOREM GCD2 == \A x \in (Nat \ {0}) : GCD({x}) = x
PROOF OMITTED

(***************************************************************************)
(* If you were to write a very rigorous proof of property 2, you would     *)
(* find that your proof uses the following property of the GCD and the two *)
(* succeeding properties of Cardinality and finite sets.  Knowledge of     *)
(* these properties as well as of GCD1 and GCD2 is not built into the      *)
(* TLAPS proof system.  If we want the prover to use these properties, we  *)
(* must tell it to.                                                        *)
(*                                                                         *)
(* Because we don't want to prove such simple mathematical facts, we       *)
(* assume them without proof.  However, assuming theorems without proof is *)
(* dangerous.  It's easy to make a mistake when writing even such simple   *)
(* properties as these.  In fact, I made several mistakes when I first     *)
(* wrote them down.  And from a false assumption, one can prove anything.  *)
(*                                                                         *)
(* To catch errors, I checked all these theorems with the TLC model        *)
(* checker.  For GCD1--GCD3, I created a model in which Nat was replaced   *)
(* by a finite set of natural numbers.  I checked the other two assertions *)
(* for finite sets of values of T and x.  (Using TLA+'s ability to name    *)
(* subexpressions of an expression, including the right-hand side of a     *)
(* defintion, I could do this without having to rewrite any formulas.)     *)
(***************************************************************************)
THEOREM GCD3 == \A T \in SUBSET (Nat \ {0}) :
                       IsFiniteSet(T) /\ (T # {}) => (GCD(T) \in Nat \ {0})
PROOF OMITTED

THEOREM CardThm == \A T : IsFiniteSet(T) =>
                             /\ Cardinality(T) \in Nat
                             /\ (Cardinality(T) = 0) <=> (T = {})
                             /\ (Cardinality(T) = 1) <=> (\E x \in T : T = {x})
PROOF OMITTED

THEOREM FiniteSetThm == \A T, x : IsFiniteSet(T) => /\ IsFiniteSet(T \cup {x})
                                                    /\ IsFiniteSet(T \ {x})
PROOF OMITTED

(***************************************************************************)
(* Below is the statement and TLAPS checked proof of property 2.  To write *)
(* the proof, I first tried proving the theorem with the following leaf    *)
(* proof.                                                                  *)
(*                                                                         *)
(*    BY InputAssump, GCD1, GCD2, GCD3, CardThm, FiniteSetThm, Z3          *)
(*    DEF Inv, TypeOK, CorrectTermination, lbl, Next, vars                 *)
(*                                                                         *)
(* This tells TLAPS to use all the facts in the BY clause and expand all   *)
(* the definitions in the DEF clause.  (The "Fact" Z3 instructs TLAPS to   *)
(* use the Z3 backend prover, which I now use as my default.)              *)
(*                                                                         *)
(* When that proof failed, I kept using the Toolbox's Decompose Proof      *)
(* command to split the proof into simpler substeps.  When doing that, it  *)
(* uses that same leaf proof for the substeps.  I then decomposed the      *)
(* substeps that it still couldn't prove.  (I removed some obviously       *)
(* unnecessary facts and definitions from the leaf proofs of substeps to   *)
(* make things easier for the prover.)                                     *)
(*                                                                         *)
(* Finally, when I reached a step that could not be automatically          *)
(* decomposed, I had to manually split the proof into steps simple enough  *)
(* for TLAPS to prove them.  I have marked all the steps that I had to     *)
(* write with the comment "|" to the left.                                 *)
(***************************************************************************)
THEOREM Inv /\ Next => Inv'
  <1> SUFFICES ASSUME Inv,
                      Next
               PROVE  Inv'
    OBVIOUS

  <1>1. ASSUME lbl
        PROVE  Inv'
    <2>1. TypeOK'
      <3>1. (/\ S \subseteq Nat \ {0}
             /\ S # {}
             /\ IsFiniteSet(S))'
        <4>1. (S \subseteq Nat \ {0})'
          BY <1>1, InputAssump, GCD1, GCD2, GCD3, CardThm, FiniteSetThm, Z3
          DEF Inv, TypeOK, CorrectTermination, lbl
        <4>2. (S # {})'
          BY <1>1, InputAssump, GCD1, GCD2, GCD3, CardThm, FiniteSetThm, Z3
          DEF Inv, TypeOK, CorrectTermination, lbl
        <4>3. IsFiniteSet(S)'
(*|*)     <5>1. CASE Cardinality(S) > 1
(*|*)         BY <5>1, <1>1, FiniteSetThm, Auto DEF Inv, TypeOK, lbl
(*|*)     <5>2. CASE ~(Cardinality(S) > 1)
(*|*)       BY <5>2, <1>1, FiniteSetThm, Z3 DEF Inv, TypeOK, lbl
(*|*)     <5>3. QED
(*|*)       BY <5>1, <5>2
        <4>4. QED
          BY <4>1, <4>2, <4>3
      <3>2. ((pc = "Done") => gcd \in Nat \ {0})'
        BY <1>1, InputAssump, GCD1, GCD2, GCD3, CardThm, FiniteSetThm, Z3
        DEF Inv, TypeOK, CorrectTermination, lbl
      <3>3. (pc \in {"lbl", "Done"})'
        BY <1>1, InputAssump, GCD1, GCD2, GCD3, CardThm, FiniteSetThm, Z3
        DEF Inv, TypeOK, CorrectTermination, lbl
      <3>4. QED
        BY <3>1, <3>2, <3>3 DEF TypeOK
    <2>2. (GCD(S) = GCD(Input))'
(*|*) <3>1. CASE Cardinality(S) > 1
(*|*)   <4>1. PICK i \in S : \E j \in {s \in S : s  >  i} :
(*|*)                           S'  =  (S  \  {j})  \union  {j  -  i}
(*|*)     BY <1>1, <3>1 DEF lbl
(*|*)   <4>2. PICK j \in {s \in S : s  >  i} :
(*|*)                           S'  =  (S  \  {j})  \union  {j  -  i}
(*|*)     BY <4>1
(*|*)   <4>3. j \in S /\ j > i
(*|*)     BY <4>2
(*|*)   <4>4. QED
(*|*)     BY <4>2, <4>3, GCD1 DEF Inv, TypeOK
(*|*) <3>2. CASE ~(Cardinality(S) > 1)
(*|*)   BY <3>2, <1>1, InputAssump, GCD1, GCD2, GCD3, CardThm, FiniteSetThm, Z3
(*|*)   DEF Inv, TypeOK, CorrectTermination, lbl
(*|*) <3>3. QED
(*|*)   BY <3>1, <3>2
    <2>3. CorrectTermination'
      BY <1>1, InputAssump, GCD1, GCD2, GCD3, CardThm, FiniteSetThm, Z3
      DEF Inv, TypeOK, CorrectTermination, lbl
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Inv

  <1>2. ASSUME pc = "Done" /\ UNCHANGED vars
        PROVE  Inv'
    BY <1>2 DEF Inv, TypeOK, CorrectTermination,  vars

  <1>3. QED
    BY <1>1, <1>2 DEF Next
=============================================================================
\* Modification History
\* Last modified Thu Jan 31 14:04:57 PST 2013 by lamport
\* Created Thu Jan 10 19:38:24 PST 2013 by lamport
