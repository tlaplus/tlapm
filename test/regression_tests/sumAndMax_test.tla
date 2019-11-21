----------------------------- MODULE sumAndMax_test -----------------------------
EXTENDS Integers, TLAPS

(***************************************************************************)
(* This is the PlusCal/TLAPS solution to the first problem in the VSTTE    *)
(* 2010 Competition.  See:                                                 *)
(*                                                                         *)
(*   http://www.macs.hw.ac.uk/vstte10/Competition.html                     *)
(*   http://www.macs.hw.ac.uk/vstte10/Competition_files/Competition.pdf    *)
(*                                                                         *)
(* Three of us (Damien Doligez, Stephan Merz, and Leslie Lamport) spent    *)
(* about an hour producing the solution--not counting the time spent       *)
(* fixing problems with TLAPS that we found.  (We were testing a newly     *)
(* released SMT backend.) Afterwards, a slight simplification of the proof *)
(* was made.                                                               *)
(*                                                                         *)
(* Here is the pseudocode of the algorithm:                                *)
(*                                                                         *)
(*    int sum, max = 0;                                                    *)
(*    int i;                                                               *)
(*    for (i=0; i<N; i++){                                                 *)
(*      if (max < a[i]){                                                   *)
(*        max = a[i];                                                      *)
(*      }                                                                  *)
(*      sum += a[i];                                                       *)
(*    }                                                                    *)
(*                                                                         *)
(* The problem is to show that, assuming N \geq 0 and a[i] \geq 0 for 0    *)
(* \leq i < N, upon termination the predicate sum \leq N * max is          *)
(* satisfied.                                                              *)
(***************************************************************************)

CONSTANT N
ASSUME NType == N \in Nat
CONSTANT a
ASSUME aType == a \in [0..(N-1) -> Nat]

(***************************************************************************
--fair algorithm SumAndMax {
  variables sum = 0, max = 0, i = 0; {
    while (i < N) {
       if (max < a[i]){max := a[i]} ;
       sum := sum + a[i];
       i := i+1;
     }
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES sum, max, i, pc

vars == << sum, max, i, pc >>

Init == (* Global variables *)
        /\ sum = 0
        /\ max = 0
        /\ i = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i < N
               THEN /\ IF max < a[i]
                          THEN /\ max' = a[i]
                          ELSE /\ TRUE
                               /\ max' = max
                    /\ sum' = sum + a[i]
                    /\ i' = i+1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << sum, max, i >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

Correctness == pc = "Done" => sum =< N*max

TypeOK == /\ sum \in Nat
          /\ max \in Nat
          /\ i \in 0..N
          /\ pc \in {"Lbl_1", "Done"}
Inv == /\ TypeOK
       /\ sum =< i * max
       /\ (pc = "Done") => (i = N)

THEOREM Spec => []Correctness
<1>1. Init => Inv
  BY NType, SMT DEF Init, Inv, TypeOK
<1>2. Inv => Correctness
  BY NType DEF Correctness, Inv, TypeOK
<1>3. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, Lbl_1
               PROVE  Inv'
    BY DEF vars, Inv, TypeOK, Next
  <2>1. CASE i = N
    BY <2>1, NType, aType, SMT DEF Inv, TypeOK, Lbl_1
  <2>2. CASE i < N
    <3> i' * max' >= i * max + max'
      BY NType, aType, <2>2, SMT DEF Inv, TypeOK, Lbl_1
    <3> QED
      BY <2>2, NType, aType, SMT DEF Inv, TypeOK, Lbl_1
  <2> QED
    BY <2>1, <2>2, NType, SMT DEF Inv, TypeOK
<1>4. QED
  (*************************************************************************)
  (* This follows from <1>1-<1>3 by trivial temporal reasoning, but TLAPS  *)
  (* does not yet handle temporal logic.                                   *)
  (*************************************************************************)
  PROOF OMITTED


=============================================================================
\* Modification History
\* Last modified Wed Nov 21 20:10:44 GMT-03:00 2012 by merz
\* Last modified Wed Nov 21 20:01:30 GMT-03:00 2012 by merz
\* Last modified Thu Oct 06 06:34:01 PDT 2011 by lamport
\* Created Mon Oct 03 03:11:15 PDT 2011 by lamport

\* Writing algorithm and model checking: 15 min
\* Writing proof, before stopping to check for tlapm bug: 24 min
\* Writing proof: 12 min.
\* Writing proof: 12 min.
