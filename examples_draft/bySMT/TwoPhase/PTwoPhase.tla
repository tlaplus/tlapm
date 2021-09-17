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

THEOREM Spec <=> PTT!TPSpec
<1>1. Init <=> PTT!TPInit
  BY SMT DEF Init, PTT!TPInit
<1>2. [Next]_vars <=> [PTT!TPNext]_<<rmState, tmState, tmPrepared, msgs>>
  BY SMT DEF vars, Next, TManager, RManager, PTT!TPNext, PTT!TMCommit, PTT!TMAbort,
         PTT!TMRcvPrepared, PTT!RMPrepare, PTT!RMChooseToAbort,
         PTT!RMRcvCommitMsg, PTT!RMRcvAbortMsg
<1>3. QED
  (*************************************************************************)
  (* Follows from <1>1, <1>2, and the definitions of Spec and PTT!TPSpec   *)
  (* by simple temporal reasoning.                                         *)
  (*************************************************************************)
  PROOF OMITTED
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
(* PTC!Spec.  For proof, we need to define the appropriate inductive       *)
(* invariant Inv of Spec, which we now do.                                 *)
(***************************************************************************)
Message ==
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type "Prepared" are    *)
  (* sent from the RM indicated by the message's rm field to the TM.       *)
  (* Messages of type "Commit" and "Abort" are broadcast by the TM, to be  *)
  (* received by all RMs.  The set msgs contains just a single copy of     *)
  (* such a message.                                                       *)
  (*************************************************************************)
  [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]

TypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM  \* \in SUBSET RM
  /\ msgs \subseteq Message   \* \in SUBSET Message


TMInv == /\ (tmState = "committed") => (tmPrepared = RM)
         /\ ([type |-> "Commit"] \in msgs) => (tmState = "committed")
         /\ ([type |-> "Abort"] \in msgs) => (tmState = "aborted")

RMInv(rm) ==
  /\ (rm \in tmPrepared) => ([type |-> "Prepared", rm |-> rm] \in msgs)
  /\ ([type |-> "Prepared", rm |-> rm] \in msgs) =>
         /\ rmState[rm] # "working"
         /\ (rmState[rm] = "aborted") => ([type |-> "Abort"] \in msgs)
  /\ (rmState[rm]= "committed") => ([type |-> "Commit"] \in msgs)

Inv == TypeOK /\ TMInv /\ (\A rm \in RM : RMInv(rm))

(***************************************************************************)
(* The TLC model checker checks in a few seconds that Inv is an invariant  *)
(* of our specification, for a model with 3 RMs.  Our spec is so simple    *)
(* that it can also check in a few seconds that Inv is an inductive        *)
(* invariant, for a model with 3 RMs.  To do this, we check that it is an  *)
(* invariant of the specification Inv /\ [][Next]_vars.  (Because of       *)
(* restrictions on TLC, to do this we must replace the last two conjuncts  *)
(* in the definition of TypeOK with the equivalent formulas                *)
(*                                                                         *)
(*   /\ tmPrepared \in SUBSET RM                                           *)
(*   /\ msgs \in SUBSET Message                                            *)
(*                                                                         *)
(* We now prove that Spec implies PTC!Spec (omitting the proofs of         *)
(* temporal steps, which are trivial for this kind of safety proof).  The  *)
(* difficult part of writing the proof was finding the inductive invariant *)
(* Inv.  Given Inv, writing the proof was a fairly mindless exercise.  The *)
(* level-one decomposition and the level-two decomposition of the          *)
(* level-one steps are standard procedures for a refinement proof.  From   *)
(* that point, I just tried TLAPS on a step and, if it failed to find a    *)
(* proof, I added another level of proof by breaking goal into subgoals    *)
(* based on the syntactical structure of the goal.  For example, if the    *)
(* goal was of the form                                                    *)
(*                                                                         *)
(*   A \/ B \/ C => D,                                                     *)
(*                                                                         *)
(* I might split the proof into the three steps                            *)
(*                                                                         *)
(*    A => D                                                               *)
(*    B => D                                                               *)
(*    C => D                                                               *)
(*                                                                         *)
(* This was rather tedious because, for technical reasons, the SMT solver  *)
(* backend cannot handle the specification Spec.  I hope that this problem *)
(* can be resolved, since the proof would not have to be decomposed into   *)
(* nearly as many levels for an SMT solver to check it.                    *)
(*                                                                         *)
(* To understand the proof, you need to know the TLA+ notation for naming  *)
(* subexpressions of a formula.  If N is the name of a formula or a        *)
(* subexpression of the formula that consists of a conjunction or          *)
(* disjunction list, then N!i is the name of the i-th conjunct of the      *)
(* list.  For example, TManager!1!2!1 is the subformula tmState = "init"   *)
(* in the definition of TManager.                                          *)
(***************************************************************************)


THEOREM Spec => PTC!Spec
<1>1. Spec => []Inv
  <2>1. Init => Inv
    BY SMT DEF Init, Inv, TypeOK, TMInv, RMInv
  <2>2. Inv /\ [Next]_vars => Inv'
    BY SMT DEF Inv, TypeOK, Message, TMInv, RMInv, Next, TManager, RManager, vars
  <2>3. QED
    (***********************************************************************)
    (* Follows immediately from <2>1, <2>2, the definition of Spec, the    *)
    (* TLA proof rule                                                      *)
    (*                                                                     *)
    (*       P /\ [N]_v => P'                                              *)
    (*     --------------------                                            *)
    (*     P /\ [][N]_v => []P                                             *)
    (*                                                                     *)
    (* and simple logic.                                                   *)
    (***********************************************************************)
    PROOF OMITTED
<1>2. Spec /\ []Inv => [][PTC!Next]_PTC!vars
  <2>1. Init => PTC!Init
    BY SMT DEF Init, PTC!Init
  <2>2. Inv /\ [Next]_vars => [PTC!Next]_PTC!vars
    <3> SUFFICES ASSUME Inv, Next
                 PROVE PTC!Next \/ UNCHANGED rmState
      BY Z3 DEFS vars, PTC!vars
    <3>2. ASSUME NEW self \in RM, RManager(self)
          PROVE  PTC!RManager(self) \/ UNCHANGED rmState
      <4>. USE DEFS Inv, TypeOK, TMInv, RMInv
      <4>3. ASSUME RManager(self)!1!3 /\ RManager(self)!2
            PROVE  PTC!RManager(self)!2!1!1 \/ UNCHANGED rmState
        BY <4>3, Z3 DEFS PTC!notCommitted, PTC!canCommit
      <4>4. ASSUME RManager(self)!1!4 /\ RManager(self)!2
            PROVE  PTC!RManager(self)!2!1!2 \/ UNCHANGED rmState
        BY <4>4, Z3 DEFS PTC!RManager, PTC!notCommitted
      <4>5. QED
      (* If <4>3 is removed, then there is a problem with set extensionality axiom.*)
        BY <3>2, <4>3, <4>4, Z3
        DEF RManager, PTC!RManager, PTC!notCommitted
    <3>3. QED
      BY <3>2, Z3 DEF Next, PTC!Next, TManager
  <2>3. QED
    (***********************************************************************)
    (* This follows immediately from <2>1, <2>2, the definition of Spec,   *)
    (* the TLA proof rule                                                  *)
    (*                                                                     *)
    (*       P /\ [M]_v => [N]_w                                           *)
    (*       --------------------                                          *)
    (*       []P /\ [][M]_v => [][N]_w                                     *)
    (*                                                                     *)
    (* and simple logic.                                                   *)
    (***********************************************************************)
    PROOF OMITTED
<1>3. QED
  (*************************************************************************)
  (* The theorem follows from <1>1, <1>2, the definition of PTC!Spec, and  *)
  (* simple logic.                                                         *)
  (*************************************************************************)
  PROOF OMITTED
=============================================================================
\* Modification History
\* Last modified Sat Nov 24 19:10:21 GMT-03:00 2012 by merz
\* Last modified Mon Nov 12 22:23:01 CET 2012 by hernanv
\* Last modified Mon May 28 11:42:05 CEST 2012 by hernanv
\* Last modified Mon May 28 01:46:19 PDT 2012 by lamport
\* Created Mon Oct 10 06:26:47 PDT 2011 by lamport
