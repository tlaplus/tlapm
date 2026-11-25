----------------------------- MODULE PTwoPhase -----------------------------
EXTENDS TLAPS
(***************************************************************************)
(* This specification describes the Two-Phase Commit protocol, in which a  *)
(* transaction manager (TM) coordinates the resource managers (RMs) to     *)
(* implement the Transaction Commit specification of module TCommit.  In   *)
(* this specification, RMs spontaneously issue Prepared messages.  We      *)
(* ignore the Prepare messages that the TM can send to the RMs.            *)
(*                                                                         *)
(* For simplicity, we also eliminate Abort messages sent by an RM when it  *)
(* decides to abort.  Such a message would cause the TM to abort the       *)
(* transaction, an event represented here by the TM spontaneously deciding *)
(* to abort.                                                               *)
(*                                                                         *)
(* This specification describes only the safety properties of the          *)
(* protocol--that is, what is allowed to happen.  What must happen would   *)
(* be described by liveness properties, which we do not specify.           *)
(***************************************************************************)
CONSTANT RM \* The set of resource managers

TM == CHOOSE tm : tm \notin RM  \* The transaction manager

(***************************************************************************
The following PlusCal algorithm is the specification of the Two-Phase
Commit algorithm.  It was written so its translation (the TLA+ formula
Spec) would be equivalent to the specification TPSpec of module
TwoPhase.

In the protocol, processes communicate with one another by sending
messages.  Since we are specifying only safety, a process is not
required to receive a message, so there is no need to model message
loss.  (There's no difference between a process not being able to
receive a message because the message was lost and a process simply
ignoring the message.) We therefore represent message passing with a
variable msgs whose value is the set of all messages that have been
sent.  Messages are never removed from msgs.  An action that, in an
implementation, would be enabled by the receipt of a certain message is
here enabled by the existence of that message in msgs.  (Receipt of the
same message twice is therefore allowed; but in this particular
protocol, receiving a message for the second time has no effect.)

In addition to msgs, the algorithm uses the following variables:

  rmState : The same as in the algorithm of module PTCommit

  tmState : The state of the TM, its value is "init", "committed",
            or "aborted".

  tmPrepared : The set of RMs from which the TM has received
               "Prepared" messages.

As in the algorithm of module PTCommit, each atomic action of the
processes is described by a PlusCal macro.  Macros are also used to
describe the sending and receiving of messages.  The PlusCal `await'
statement is equivalent to the `when' statement, introducing an
enabling condition.

 `.
--algorithm TwoPhaseCommit {
  variables rmState = [rm \in RM |-> "working"],
            tmState = "init",
            tmPrepared   = {},
            msgs = {} ;
  macro SendMsg(m) { msgs := msgs \cup {m} }
  macro RcvMsg(m) { await m \in msgs }
  macro TMRcvPrepared() {
    (***********************************************************************)
    (* The TM receives a "Prepared" message from some resource manager.    *)
    (***********************************************************************)
    await tmState = "init";
    with (rm \in RM) {
      RcvMsg([type |-> "Prepared", rm |-> rm]);
      tmPrepared := tmPrepared \cup {rm}
     }
   }
  macro TMCommit() {
    (***********************************************************************)
    (* The TM commits the transaction; enabled iff the TM is in its        *)
    (* initial state and every RM has sent a "Prepared" message.           *)
    (***********************************************************************)
    await /\ tmState = "init"
          /\ tmPrepared = RM ;
    tmState := "committed" ;
    SendMsg([type |-> "Commit"])
   }
  macro TMAbort() {
    (***********************************************************************)
    (* The TM spontaneously aborts the transaction.                        *)
    (***********************************************************************)
    await tmState = "init" ;
    tmState := "aborted" ;
    SendMsg([type |-> "Abort"])
   }
  macro RMPrepare(rm) {
    (***********************************************************************)
    (* Resource manager rm prepares.                                       *)
    (***********************************************************************)
    await rmState[rm] = "working" ;
    rmState[rm] := "prepared" ;
    SendMsg([type |-> "Prepared", rm |-> rm])
   }
  macro RMChooseToAbort(rm) {
    (***********************************************************************)
    (* Resource manager rm spontaneously decides to abort.  As noted       *)
    (* above, rm does not send any message in our simplified spec.         *)
    (***********************************************************************)
    await rmState[rm] = "working" ;
    rmState[rm] := "aborted"
   }
  macro RMRcvCommitMsg(rm) {
    (***********************************************************************)
    (* Resource manager rm is told by the TM to commit.                    *)
    (***********************************************************************)
    RcvMsg([type |-> "Commit"]) ;
    rmState[rm] := "committed"
   }
  macro RMRcvAbortMsg(rm) {
    (***********************************************************************)
    (* Resource manager rm is told by the TM to abort.                     *)
    (***********************************************************************)
    RcvMsg ([type |-> "Abort"]) ;
    rmState[rm] := "aborted"
   }
  process (TManager = TM) {
    tmstart: while (TRUE) {
               either TMCommit() or TMAbort() or TMRcvPrepared()
              }
   }
  process (RManager \in RM) {
    rmstart: while (TRUE) {
               either RMPrepare(self) or RMChooseToAbort(self)
                 or RMRcvCommitMsg(self) or RMRcvAbortMsg(self)
              }
   }
}
 .'

 The following is the translation of the PlusCal algorithm.  A careful
 comparison of the definitions shows that formula Spec is essentially
 the same as formula TPSpec of module TwoPhase.
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES rmState, tmState, tmPrepared, msgs

vars == << rmState, tmState, tmPrepared, msgs >>

ProcSet == {TM} \cup (RM)

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ tmPrepared = {}
        /\ msgs = {}

TManager == /\ \/ /\ /\ tmState = "init"
                     /\ tmPrepared = RM
                  /\ tmState' = "committed"
                  /\ msgs' = (msgs \cup {([type |-> "Commit"])})
                  /\ UNCHANGED tmPrepared
               \/ /\ tmState = "init"
                  /\ tmState' = "aborted"
                  /\ msgs' = (msgs \cup {([type |-> "Abort"])})
                  /\ UNCHANGED tmPrepared
               \/ /\ tmState = "init"
                  /\ \E rm \in RM:
                       /\ ([type |-> "Prepared", rm |-> rm]) \in msgs
                       /\ tmPrepared' = (tmPrepared \cup {rm})
                  /\ UNCHANGED <<tmState, msgs>>
            /\ UNCHANGED rmState


RManager(self) == /\ \/ /\ rmState[self] = "working"
                        /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                        /\ msgs' = (msgs \cup {([type |-> "Prepared", rm |-> self])})
                     \/ /\ rmState[self] = "working"
                        /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                        /\ msgs' = msgs
                     \/ /\ ([type |-> "Commit"]) \in msgs
                        /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                        /\ msgs' = msgs
                     \/ /\ ([type |-> "Abort"]) \in msgs
                        /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                        /\ msgs' = msgs
                  /\ UNCHANGED << tmState, tmPrepared >>


Next == TManager
           \/ (\E self \in RM: RManager(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

(***************************************************************************)
(* As we did for the specifications of modules PTCommit and TCommit, we    *)
(* now check that specification Spec of this module is equivalent to       *)
(* specification TPSpec of module TwoPhase.                                *)
(***************************************************************************)
PTT == INSTANCE TwoPhase

THEOREM TPEquiv == Spec <=> PTT!TPSpec
<1>1. Init <=> PTT!TPInit
  BY SMT DEF Init, PTT!TPInit
<1>2. [Next]_vars <=> [PTT!TPNext]_(PTT!vars)
  BY SMT DEF vars, Next, TManager, RManager, PTT!TPNext, PTT!TMCommit, PTT!TMAbort,
         PTT!TMRcvPrepared, PTT!RMPrepare, PTT!RMChooseToAbort,
         PTT!RMRcvCommitMsg, PTT!RMRcvAbortMsg, PTT!vars 
<1>3. QED  BY <1>1, <1>2, PTL DEF Spec, PTT!TPSpec

-----------------------------------------------------------------------------
(***************************************************************************)
(* We now show that the Two-Phase Commit algorithm is a transaction commit *)
(* algorithm by showing that it refines the specification of transaction   *)
(* commit of module PTCommit.  This means showing that formula Spec of     *)
(* this module, our specification of two-phase commit, implies formula     *)
(* Spec of module PTCommit, our specification of transaction commit.  More *)
(* precisely, we prove that formula Spec of this module implies formula    *)
(* PTC!Spec, where PTC!Spec is the formula obtained by substituting for    *)
(* parameters RM and rmState of module PTCommit the correspondingly-named  *)
(* parameters of the current module.  The following INSTANCE statement     *)
(* defines PTC!Spec, as well as PTC!F for every other symbol F defined in  *)
(* module PTCommit.                                                        *)
(***************************************************************************)
PTC == INSTANCE PTCommit

(***************************************************************************)
(* TLC can in a few seconds check that Spec implies PTC!Spec for a model   *)
(* with 3 RMs, which is enough to inspire confidence in the correctness of *)
(* the refinement.  However, it is not hard to prove that Spec implies     *)
(* PTC!Spec. Instead of proving refinement by identifying a suitable       *)
(* invariant, we reuse the existing refinement proof of module TwoPhase    *)
(* and the fact that the specifications of the TLA+ and PlusCal versions   *)
(* are equivalent that we already established previously. It is a little   *)
(* tedious that in order to do so, we need to prove a bridging lemma       *)
(* relating the instantiated specifications: the PM does not recognize     *)
(* that these are in fact the same formulas.                               *)
(***************************************************************************)
TC == INSTANCE TCommit

LEMMA Bridge ==
    /\ TC!TCSpec <=> PTT!TC!TCSpec
    /\ TC!TCSpec <=> PTC!TC!TCSpec
<1>1. TC!TCSpec <=> PTT!TC!TCSpec
  BY PTL 
     DEF TC!TCSpec, TC!TCInit, TC!TCNext, TC!Prepare, TC!Decide, 
         TC!canCommit, TC!notCommitted,
         PTT!TC!TCSpec, PTT!TC!TCInit, PTT!TC!TCNext, PTT!TC!Prepare, PTT!TC!Decide, 
         PTT!TC!canCommit, PTT!TC!notCommitted
<1>2. TC!TCSpec <=> PTC!TC!TCSpec
  BY PTL 
     DEF TC!TCSpec, TC!TCInit, TC!TCNext, TC!Prepare, TC!Decide, 
         TC!canCommit, TC!notCommitted,
         PTC!TC!TCSpec, PTC!TC!TCInit, PTC!TC!TCNext, PTC!TC!Prepare, PTC!TC!Decide, 
         PTC!TC!canCommit, PTC!TC!notCommitted
<1>. QED  BY <1>1, <1>2

THEOREM Refinement == Spec => PTC!Spec
BY TPEquiv, PTC!TCEquiv, PTT!Refinement, Bridge

=============================================================================
\* Created Mon Oct 10 06:26:47 PDT 2011 by lamport
