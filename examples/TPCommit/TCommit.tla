------------------------------- MODULE TCommit ------------------------------
EXTENDS TLAPS 

CONSTANT RM       \* The set of participating resource managers
VARIABLE rmState  \* `rmState[rm]' is the state of resource manager rm.
-----------------------------------------------------------------------------
TCTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit ==   rmState = [rm \in RM |-> "working"]
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)

canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}
  (*************************************************************************)
  (* True iff all RMs are in the "prepared" or "committed" state.          *)
  (*************************************************************************)

notCommitted == \A rm \in RM : rmState[rm] # "committed"
  (*************************************************************************)
  (* True iff neither no resource manager has decided to commit.           *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the RMs, and then    *)
(* define the complete next-state action of the specification to be the    *)
(* disjunction of the possible RM actions.                                 *)
(***************************************************************************)
Prepare(rm) == /\ rmState[rm] = "working"
               /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]

Decide(rm)  == \/ /\ rmState[rm] = "prepared"
                  /\ canCommit
                  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
               \/ /\ rmState[rm] \in {"working", "prepared"}
                  /\ notCommitted
                  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]

TCNext == \E rm \in RM : Prepare(rm) \/ Decide(rm)
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
-----------------------------------------------------------------------------
TCSpec == TCInit /\ [][TCNext]_rmState
  (*************************************************************************)
  (* The complete specification of the protocol.                           *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now assert invariance properties of the specification.               *)
(***************************************************************************)
TCConsistent ==
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
<1>1. TCInit => TCTypeOK /\ TCConsistent
  BY DEF TCInit, TCTypeOK, TCConsistent
<1>2. TCTypeOK /\ TCConsistent /\ [TCNext]_rmState => (TCTypeOK /\ TCConsistent)'
  BY DEF TCTypeOK, TCConsistent, TCNext, Prepare, Decide, canCommit, notCommitted
<1>. QED  BY <1>1, <1>2, PTL DEF TCSpec
  (*************************************************************************)
  (* Asserts that TCTypeOK and TCInvariant are invariants of the protocol. *)
  (*************************************************************************)
=============================================================================
