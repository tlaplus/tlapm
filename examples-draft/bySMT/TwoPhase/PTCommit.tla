------------------------------ MODULE PTCommit ------------------------------
EXTENDS TLAPS
CONSTANT RM       \* The set of participating resource managers

(***************************************************************************
--algorithm TransactionCommit {
  variable rmState = [rm \in RM |-> "working"] ;
  define {
    canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}
      (*********************************************************************)
      (* True iff all RMs are in the "prepared" or "committed" state.      *)
      (*********************************************************************)
    notCommitted == \A rm \in RM : rmState[rm] # "committed"
      (*********************************************************************)
      (* True iff neither no resource manager has decided to commit.       *)
      (*********************************************************************)
   }
  macro Prepare(p) {
    when rmState[p] = "working";
    rmState[p] := "prepared" ;
   }

  macro Decide(p) {
    either { when /\ rmState[p] = "prepared"
                  /\ canCommit ;
             rmState[p] := "committed"
           }
    or     { when /\ rmState[p] \in {"working", "prepared"}
                  /\ notCommitted ;
             rmState[p] := "aborted"
           }
   }
  process (RManager \in RM) {
    start: while (TRUE) { either Prepare(self) or Decide(self) }
   }
}

 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLE rmState

(* define statement *)
canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}



notCommitted == \A rm \in RM : rmState[rm] # "committed"


vars == << rmState >>

ProcSet == (RM)

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]

RManager(self) == \/ /\ rmState[self] = "working"
                     /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                  \/ /\ \/ /\ /\ rmState[self] = "prepared"
                              /\ canCommit
                           /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                        \/ /\ /\ rmState[self] \in {"working", "prepared"}
                              /\ notCommitted
                           /\ rmState' = [rmState EXCEPT ![self] = "aborted"]


Next == (\E self \in RM: RManager(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
TypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TC == INSTANCE TCommit

THEOREM Spec <=> TC!TCSpec
  <1>1. Init <=> TC!TCInit
    BY DEF Init, TC!TCInit
  <1>2. [Next]_rmState <=> [TC!TCNext]_rmState
    BY DEF Next, ProcSet, RManager, canCommit, notCommitted,
           TC!TCNext, TC!Prepare, TC!Decide, TC!canCommit, TC!notCommitted
  <1>3. QED
    (***********************************************************************)
    (* Follows from <1>1 and <1>2 by trivial temporal logic.               *)
    (***********************************************************************)
    PROOF OMITTED

=============================================================================
\* Modification History
\* Last modified Mon Oct 10 07:24:52 PDT 2011 by lamport
\* Created Mon Oct 10 05:31:02 PDT 2011 by lamport
