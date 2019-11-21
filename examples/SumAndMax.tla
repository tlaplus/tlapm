----------------------------- MODULE SumAndMax -----------------------------
EXTENDS Integers, TLAPS

(***************************************************************************)
(* This is the PlusCal/TLAPS solution to the first problem in the VSTTE    *)
(* 2010 Competition.  See:                                                 *)
(*                                                                         *)
(*   http://www.macs.hw.ac.uk/vstte10/Competition.html                     *)
(*   http://www.macs.hw.ac.uk/vstte10/Competition_files/Competition.pdf    *)
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
  BY NType, aType, SMT DEF Inv, TypeOK, Next, vars, Lbl_1
<1>. QED  BY <1>1, <1>2, <1>3, PTL DEF Spec


=============================================================================
