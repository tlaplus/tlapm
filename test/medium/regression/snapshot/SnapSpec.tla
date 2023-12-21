----------------------------- MODULE SnapSpec -----------------------------
CONSTANT Proc, Val

PUnion(Q) == UNION {Q[p] : p \in Proc}

(******
--algorithm SnapSpec
{ variables  myVals = [i \in Proc |-> {}],
             nextout = [i \in Proc |-> {}];
  process (Pr \in Proc)
     variable out = {};
     { A: while (TRUE)
           {    with (v \in Val) { myVals[self] := myVals[self] \cup {v} };
             B: with (V \in {W \in SUBSET PUnion(myVals) :
                                /\ myVals[self] \subseteq W
                                /\ PUnion(nextout) \subseteq W })
                 { nextout[self] := V };
             C: either out := nextout[self]
                or     goto B ;
           }
     }
}
*****)
\* BEGIN TRANSLATION
VARIABLES myVals, nextout, pc, out

vars == << myVals, nextout, pc, out >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ myVals = [i \in Proc |-> {}]
        /\ nextout = [i \in Proc |-> {}]
        (* Process Pr *)
        /\ out = [self \in Proc |-> {}]
        /\ pc = [self \in ProcSet |-> "A"]

A(self) == /\ pc[self] = "A"
           /\ \E v \in Val:
                myVals' = [myVals EXCEPT ![self] = myVals[self] \cup {v}]
           /\ pc' = [pc EXCEPT ![self] = "B"]
           /\ UNCHANGED << nextout, out >>

B(self) == /\ pc[self] = "B"
           /\ \E V \in {W \in SUBSET PUnion(myVals) :
                           /\ myVals[self] \subseteq W
                           /\ PUnion(nextout) \subseteq W }:
                nextout' = [nextout EXCEPT ![self] = V]
           /\ pc' = [pc EXCEPT ![self] = "C"]
           /\ UNCHANGED << myVals, out >>

C(self) == /\ pc[self] = "C"
           /\ \/ /\ out' = [out EXCEPT ![self] = nextout[self]]
                 /\ pc' = [pc EXCEPT ![self] = "A"]
              \/ /\ pc' = [pc EXCEPT ![self] = "B"]
                 /\ out' = out
           /\ UNCHANGED << myVals, nextout >>

Pr(self) == A(self) \/ B(self) \/ C(self)

Next == (\E self \in Proc: Pr(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* It's always a good idea to write and have TLC check a type invariant.   *)
(***************************************************************************)
TypeOK == /\ myVals \in [Proc -> SUBSET Val]
          /\ out \in [Proc -> PUnion(myVals)]
-----------------------------------------------------------------------------
(***************************************************************************)
(* Specification BigSpec is the same as the specification Spec produced by *)
(* translating the SnapSpec algorithm's code except that it allows a step, *)
(* enabled when some process p is at control point A, that moves some set  *)
(* of processes at control point C to control point B -- just as if they   *)
(* had all simulateously executed statement C, choosing to perform the     *)
(* second clause of the enabled/or statement.  Spec BigSpec has the same   *)
(* initial predicate as Spec.  It's next-state action BigNext is the       *)
(* disjunction of the next-state action of algorithm SnapSpec with an      *)
(* action that describes the extra step the BegSpec allows.                *)
(***************************************************************************)
BigNext == \/ Next
           \/ \E p \in Proc :
              /\ pc[p] = "A"
              /\ \E P \in SUBSET (Proc \ {p}) :
                    /\ \A q \in P : pc[q] = "C"
                    /\ pc' = [q \in Proc |-> IF q \in P THEN "B"
                                                        ELSE pc[q]]
                    /\ UNCHANGED << myVals, nextout,  out>>

BigSpec == Init /\ [][BigNext]_vars
=============================================================================
\* Modification History
\* Last modified Fri Jul 20 11:48:06 PDT 2012 by lamport
\* Created Wed Jul 04 23:50:00 PDT 2012 by lamport
