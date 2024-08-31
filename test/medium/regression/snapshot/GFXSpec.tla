----------------------------- MODULE GFXSpec -----------------------------
(***************************************************************************)
(* The EXTENDS statement imports the standard module FiniteSets, which     *)
(* defines a few useful operators for reasoning about finite sets,         *)
(* including Cardinality.                                                  *)
(***************************************************************************)
EXTENDS FiniteSets

(***************************************************************************)
(* The CONSTANT statement declares Proc to be an unspecified constant.     *)
(* There's no need (and no way) to specify that Proc is a set because TLA+ *)
(* is based on ZF set theory, so value is a set.                           *)
(***************************************************************************)
CONSTANT Proc
-----------------------------------------------------------------------------
(***************************************************************************
--algorithm GFXSpec
{ variable result = [p \in Proc |-> {}]
  process (Pr \in Proc)
    { A: with ( P \in { Q \in SUBSET Proc :
                           /\ self \in Q
                           /\ \A p \in Proc\{self}:
                                \/ Cardinality (result[p]) # Cardinality(Q)
                                \/ Q = result[p]
                        } )
             { result[self] := P }
    }
}
 ***************************************************************************)
(***************************************************************************)
(* The algorithm is automatically translated to the stuff between the      *)
(* BEGIN TRANSLATION and END TRANSLATION comments.                         *)
(***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES result, pc

vars == << result, pc >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ result = [p \in Proc |-> {}]
        /\ pc = [self \in ProcSet |-> "A"]

A(self) == /\ pc[self] = "A"
           /\ \E P \in { Q \in SUBSET Proc :
                            /\ self \in Q
                            /\ \A p \in Proc\{self}:
                                 \/ Cardinality (result[p]) # Cardinality(Q)
                                 \/ Q = result[p]
                         }:
                result' = [result EXCEPT ![self] = P]
           /\ pc' = [pc EXCEPT ![self] = "Done"]

Pr(self) == A(self)

Next == (\E self \in Proc: Pr(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* We can check the specification for trivial "type errors" with TLC by    *)
(* having it check that the following predicates TypeOK and GFXCorrect are *)
(* invariants.                                                             *)
(***************************************************************************)
TypeOK == result \in [Proc -> SUBSET Proc]

Done(i) == pc[i] = "Done"

GFXCorrect == \A i, j \in Proc :
                /\ Done(i) /\ Done(j)
                /\ Cardinality(result[i]) = Cardinality(result[j])
                => (result[i] = result[j])
=============================================================================
\* Modification History
\* Last modified Fri Jul 20 14:07:01 PDT 2012 by lamport
\* Created Fri Jul 06 03:18:28 PDT 2012 by lamport
