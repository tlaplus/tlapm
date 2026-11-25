------------------------------- MODULE TwoPhase -----------------------------
EXTENDS TLAPS
(***************************************************************************)
(* This specification describes the Two-Phase Commit protocol, in which a  *)
(* transaction manager (TM) coordinates the resource managers (RMs) to     *)
(* implement the Transaction Commit specification of module $TCommit$.  In *)
(* this specification, RMs spontaneously issue $Prepared$ messages.  We    *)
(* ignore the $Prepare$ messages that the TM can send to the               *)
(* RMs.\vspace{.4em}                                                       *)
(*                                                                         *)
(* For simplicity, we also eliminate $Abort$ messages sent by an RM when   *)
(* it decides to abort.  Such a message would cause the TM to abort the    *)
(* transaction, an event represented here by the TM spontaneously deciding *)
(* to abort.\vspace{.4em}                                                  *)
(*                                                                         *)
(* This specification describes only the safety properties of the          *)
(* protocol--that is, what is allowed to happen.  What must happen would   *)
(* be described by liveness properties, which we do not specify.           *)
(***************************************************************************)
CONSTANT RM \* The set of resource managers

VARIABLES
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received $"Prepared"$
                 \* messages.
  msgs

vars == <<rmState, tmState, tmPrepared, msgs>> 

    (***********************************************************************)
    (* In the protocol, processes communicate with one another by sending  *)
    (* messages.  Since we are specifying only safety, a process is not    *)
    (* required to receive a message, so there is no need to model message *)
    (* loss.  (There's no difference between a process not being able to   *)
    (* receive a message because the message was lost and a process simply *)
    (* ignoring the message.)  We therefore represent message passing with *)
    (* a variable $msgs$ whose value is the set of all messages that have  *)
    (* been sent.  Messages are never removed from $msgs$.  An action      *)
    (* that, in an implementation, would be enabled by the receipt of a    *)
    (* certain message is here enabled by the existence of that message in *)
    (* $msgs$.  (Receipt of the same message twice is therefore allowed;   *)
    (* but in this particular protocol, receiving a message for the second *)
    (* time has no effect.)                                                *)
    (***********************************************************************)

Message ==
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type $"Prepared"$ are  *)
  (* sent from the RM indicated by the message's $rm$ field to the TM\@.   *)
  (* Messages of type $"Commit"$ and $"Abort"$ are broadcast by the TM, to *)
  (* be received by all RMs.  The set $msgs$ contains just a single copy   *)
  (* of such a message.                                                    *)
  (*************************************************************************)
  [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]

TPTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Message

TPInit ==
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgs = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the TM's actions, then the RMs' actions.                                *)
(***************************************************************************)
TMRcvPrepared(rm) ==
  (*************************************************************************)
  (* The TM receives a $"Prepared"$ message from resource manager $rm$.    *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit ==
  (*************************************************************************)
  (* The TM commits the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a $"Prepared"$ message.                   *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
  (*************************************************************************)
  (* The TM spontaneously aborts the transaction.                          *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ prepares.                                       *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared>>

RMChooseToAbort(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ spontaneously decides to abort.  As noted       *)
  (* above, $rm$ does not send any message in our simplified spec.         *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvCommitMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to commit.                    *)
  (*************************************************************************)
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbortMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to abort.                     *)
  (*************************************************************************)
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TPNext ==
  \/ TMCommit \/ TMAbort
  \/ \E rm \in RM :
       TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
         \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)

TPSpec == TPInit /\ [][TPNext]_vars
  (*************************************************************************)
  (* The complete spec of the Two-Phase Commit protocol.                   *)
  (*************************************************************************)

-----------------------------------------------------------------------------
(***************************************************************************)
(* We now show that the Two-Phase Commit algorithm is a transaction commit *)
(* algorithm by showing that it refines the specification of transaction   *)
(* commit of module TCommit.  This means showing that formula Spec of      *)
(* this module, our specification of two-phase commit, implies formula     *)
(* Spec of module TCommit, our specification of transaction commit.        *)
(***************************************************************************)
TC == INSTANCE TCommit

(***************************************************************************)
(* TLC can in a few seconds check that Spec implies TC!Spec for a model    *)
(* with 3 RMs, which is enough to inspire confidence in the correctness of *)
(* the refinement.  However, it is not hard to prove that Spec implies     *)
(* TC!Spec.  For proof, we need to define the appropriate inductive        *)
(* invariant Inv of Spec, which we now do.                                 *)
(***************************************************************************)

TMInv == /\ (tmState = "committed") => (tmPrepared = RM)
         /\ ([type |-> "Commit"] \in msgs) => (tmState = "committed")
         /\ ([type |-> "Abort"] \in msgs) => (tmState = "aborted")

RMInv(rm) ==
  /\ (rm \in tmPrepared) => ([type |-> "Prepared", rm |-> rm] \in msgs)
  /\ ([type |-> "Prepared", rm |-> rm] \in msgs) =>
         /\ rmState[rm] # "working"
         /\ (rmState[rm] = "aborted") => ([type |-> "Abort"] \in msgs)
  /\ (rmState[rm]= "committed") => ([type |-> "Commit"] \in msgs)

Inv == TPTypeOK /\ TMInv /\ (\A rm \in RM : RMInv(rm))

THEOREM Invariant == TPSpec => []Inv
<1>1. TPInit => Inv
  BY DEF TPInit, Inv, TPTypeOK, TMInv, RMInv
<1>2. Inv /\ [TPNext]_vars => Inv'
  BY DEF Inv, TPTypeOK, TMInv, RMInv, 
         TPNext, TMCommit, TMAbort, TMRcvPrepared, RMPrepare,
         RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg, vars, Message
<1>. QED  BY <1>1, <1>2, PTL DEF TPSpec


THEOREM Refinement == TPSpec => TC!TCSpec
<1>1. TPInit => TC!TCInit 
  BY DEF TPInit, TC!TCInit
<1>2. Inv /\ [TPNext]_vars => [TC!TCNext]_rmState
  BY DEF Inv, TPTypeOK, TMInv, RMInv, 
         TPNext, TMCommit, TMAbort, TMRcvPrepared, RMPrepare,
         RMChooseToAbort, RMRcvCommitMsg, RMRcvAbortMsg, vars, Message,
         TC!TCNext, TC!Prepare, TC!Decide, TC!canCommit, TC!notCommitted
<1>. QED  BY <1>1, <1>2, Invariant, PTL DEF TPSpec, TC!TCSpec

=============================================================================
