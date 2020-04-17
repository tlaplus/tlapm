
---------------------------- MODULE BPConProof_test ------------------------------
(***************************************************************************)
(* This module specifies a Byzantine Paxos algorithm--a version of Paxos   *)
(* in which failed acceptors and leaders can be malicious.  It is an       *)
(* abstraction and generalization of the Castro-Liskov algorithm in        *)
(*                                                                         *)
(*    author = "Miguel Castro and Barbara Liskov",                         *)
(*    title = "Practical byzantine fault tolerance and proactive           *)
(*             recovery",                                                  *)
(*    journal = ACM Transactions on Computer Systems,                      *)
(*    volume = 20,                                                         *)
(*    number = 4,                                                          *)
(*    year = 2002,                                                         *)
(*    pages = "398--461"                                                   *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, TLAPS

-----------------------------------------------------------------------------
(***************************************************************************)
(* We need the following trivial axioms and theorem about finite sets.     *)
(***************************************************************************)
AXIOM EmptySetFinite == IsFiniteSet({})

AXIOM SingletonSetFinite == \A e : IsFiniteSet({e})

AXIOM ImageOfFiniteSetFinite ==
         \A S, f : IsFiniteSet(S) => IsFiniteSet({f[x] : x \in S})

AXIOM SubsetOfFiniteSetFinite ==
        \A S, T : IsFiniteSet(T) /\ (S \subseteq T) => IsFiniteSet(S)

AXIOM UnionOfFiniteSetsFinite ==
        \A S, T : IsFiniteSet(T) /\ IsFiniteSet(S)  => IsFiniteSet(S \cup T)

THEOREM OnePlusFinite == \A S, e : IsFiniteSet(S) => IsFiniteSet(S \cup {e})
BY SingletonSetFinite, UnionOfFiniteSetsFinite

(***************************************************************************)
(* Testing that the following formula is true provides a check for typos   *)
(* in the axioms above.                                                    *)
(***************************************************************************)
TestAxioms ==
   \* SingletonSetFinite
   /\ \A e \in 1..3 : IsFiniteSet({e})

   \* ImageOfFiniteSetFinite
   /\ \A S, T \in SUBSET (1..4): \A f \in [S -> T] :
        IsFiniteSet(S) => IsFiniteSet({f[x] : x \in S})

   \* SubsetOfFiniteSetFinite
   /\ \A S, T \in SUBSET (1..4) :
        IsFiniteSet(T) /\ (S \subseteq T) => IsFiniteSet(S)

   \* UnionOfFiniteSetsFinite
   /\ \A S, T \in SUBSET (1..4) :
        IsFiniteSet(T) /\ IsFiniteSet(S)  => IsFiniteSet(S \cup T)
----------------------------------------------------------------------------
(***************************************************************************)
(* The sets Value and Ballot are the same as in the Voting and             *)
(* PConProof specs.                                                        *)
(***************************************************************************)
CONSTANT Value

Ballot == Nat

(***************************************************************************)
(* As in module PConProof, we define None to be an unspecified value that  *)
(* is not an element of Value.                                             *)
(***************************************************************************)
None == CHOOSE v : v \notin Value
-----------------------------------------------------------------------------
(***************************************************************************)
(* We pretend that which acceptors are good and which are malicious is     *)
(* specified in advance.  Of course, the algorithm executed by the good    *)
(* acceptors makes no use of which acceptors are which.  Hence, we can     *)
(* think of the sets of good and malicious acceptors as "prophecy          *)
(* constants" that are used only for showing that the algorithm implements *)
(* the PCon algorithm.                                                     *)
(*                                                                         *)
(* We can assume that a maximal set of acceptors are bad, since a bad      *)
(* acceptor is allowed to do anything--including ating like a good one.    *)
(*                                                                         *)
(* The basic idea is that the good acceptors try to execute the Paxos      *)
(* consensus algorithm, while the bad acceptors may try to prevent them.   *)
(*                                                                         *)
(* We do not distinguish between faulty and non-faulty leaders.  Safety    *)
(* must be preserved even if all leaders are malicious, so we allow any    *)
(* leader to send any syntactically correct message at any time.  (In an   *)
(* implementation, syntactically incorrect messages are simply ignored by  *)
(* non-faulty acceptors and have no effect.) Assumptions about leader      *)
(* behavior are required only for liveness.                                *)
(***************************************************************************)
CONSTANTS Acceptor,       \* The set of good (non-faulty) acceptors.
          FakeAcceptor,   \* The set of possibly malicious (faulty) acceptors.
          ByzQuorum,
            (***************************************************************)
            (* A Byzantine quorum is set of acceptors that includes a      *)
            (* quorum of good ones.  In the case that there are 2f+1 good  *)
            (* acceptors and f bad ones, a Byzantine quorum is any set of  *)
            (* 2f+1 acceptors.                                             *)
            (***************************************************************)
          WeakQuorum
            (***************************************************************)
            (* A weak quorum is a set of acceptors that includes at least  *)
            (* one good one.  If there are f bad acceptors, then a weak    *)
            (* quorum is any set of f+1 acceptors.                         *)
            (***************************************************************)

(***************************************************************************)
(* We define ByzAcceptor to be the set of all real or fake acceptors.      *)
(***************************************************************************)
ByzAcceptor == Acceptor \cup FakeAcceptor

(***************************************************************************)
(* As in the Paxos consensus algorithm, we assume that the set of ballot   *)
(* numbers and -1 is disjoint from the set of all (real and fake)          *)
(* acceptors.                                                              *)
(***************************************************************************)
ASSUME BallotAssump == (Ballot \cup {-1}) \cap ByzAcceptor = {}

(***************************************************************************)
(* The following are the assumptions about acceptors and quorums that are  *)
(* needed to ensure safety of our algorithm.                               *)
(***************************************************************************)
ASSUME BQA ==
          /\ Acceptor \cap FakeAcceptor = {}
          /\ \A Q \in ByzQuorum : Q \subseteq ByzAcceptor
          /\ \A Q1, Q2 \in ByzQuorum : Q1 \cap Q2 \cap Acceptor # {}
          /\ \A Q \in WeakQuorum : /\ Q \subseteq ByzAcceptor
                                   /\ Q \cap Acceptor # {}

(***************************************************************************)
(* The following assumption is not needed for safety, but it will be       *)
(* needed to ensure liveness.                                              *)
(***************************************************************************)
ASSUME BQLA ==
          /\ \E Q \in ByzQuorum : Q \subseteq Acceptor
          /\ \E Q \in WeakQuorum : Q \subseteq Acceptor
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the set BMessage of all possible messages.                *)
(***************************************************************************)
1aMessage == [type : {"1a"},  bal : Ballot]
  (*************************************************************************)
  (* Type 1a messages are the same as in module PConProof.                 *)
  (*************************************************************************)

1bMessage ==
  (*************************************************************************)
  (* A 1b message serves the same function as a 1b message in ordinary     *)
  (* Paxos, where the mbal and mval components correspond to the mbal and  *)
  (* mval components in the 1b messages of PConProof.  The m2av component  *)
  (* is set containing all records with val and bal components equal to    *)
  (* the corresponding of components of a 2av message that the acceptor    *)
  (* has sent, except containing for each val only the record              *)
  (* corresponding to the 2av message with the highest bal component.      *)
  (*************************************************************************)
  [type : {"1b"}, bal : Ballot,
   mbal : Ballot \cup {-1}, mval : Value \cup {None},
   m2av : SUBSET [val : Value, bal : Ballot],
   acc : ByzAcceptor]

1cMessage ==
  (*************************************************************************)
  (* Type 1c messages are the same as in PConProof.                        *)
  (*************************************************************************)
  [type : {"1c"}, bal : Ballot, val : Value]

2avMessage ==
  (*************************************************************************)
  (* When an acceptor receives a 1c message, it relays that message's      *)
  (* contents to the other acceptors in a 2av message.  It does this only  *)
  (* for the first 1c message it receives for that ballot; it can receive  *)
  (* a second 1c message only if the leader is malicious, in which case it *)
  (* ignores that second 1c message.                                       *)
  (*************************************************************************)
   [type : {"2av"}, bal : Ballot, val : Value, acc : ByzAcceptor]

2bMessage == [type : {"2b"}, acc : ByzAcceptor, bal : Ballot, val : Value]
  (*************************************************************************)
  (* 2b messages are the same as in ordinary Paxos.                        *)
  (*************************************************************************)

BMessage ==
  1aMessage \cup 1bMessage \cup 1cMessage \cup 2avMessage \cup 2bMessage

(***************************************************************************)
(* We will need the following simple fact about these sets of messages.    *)
(***************************************************************************)
LEMMA BMessageLemma ==
         \A m \in BMessage :
           /\ (m \in 1aMessage) <=>  (m.type = "1a")
           /\ (m \in 1bMessage) <=>  (m.type = "1b")
           /\ (m \in 1cMessage) <=>  (m.type = "1c")
           /\ (m \in 2avMessage) <=>  (m.type = "2av")
           /\ (m \in 2bMessage) <=>  (m.type = "2b")
<1>1. /\ \A m \in 1aMessage : m.type = "1a"
      /\ \A m \in 1bMessage : m.type = "1b"
      /\ \A m \in 1cMessage : m.type = "1c"
      /\ \A m \in 2avMessage : m.type = "2av"
      /\ \A m \in 2bMessage : m.type = "2b"
  BY DEF 1aMessage, 1bMessage, 1cMessage, 2avMessage, 2bMessage
<1>2. QED
  BY <1>1 DEF BMessage
-----------------------------------------------------------------------------


(****************************************************************************
We now give the algorithm.  The basic idea is that the set Acceptor of
real acceptors emulate an execution of the PCon algorithm with
Acceptor as its set of acceptors.  Of course, they must do that
without knowing which of the other processes in ByzAcceptor are real
acceptors and which are fake acceptors.  In addition, they don't know
whether a leader is behaving according to the PCon algorithm or if it
is malicious.

The main idea of the algorithm is that, before performing an action of
the PCon algorithm, a good acceptor determines that this action is
actually enabled in that algorithm.  Since an action is enabled by the
receipt of one or more messages, the acceptor has to determine that
the enabling messages are legal PCon messages.  Because algorithm PCon
allows a 1a message to be sent at any time, the only acceptor action
whose enabling messages must be checked is the Phase2b action.  It is
enabled iff the appropriate 1c message and 2a message are legal.  The
1c message is legal iff the leader has received the necessary 1b
messages.  The acceptor therefore maintains a set of 1b messages that
it knows have been sent, and checks that those 1b messages enable the
sending of the 1c message.

A 2a message is legal in the PCon algorithm iff (i) the corresponding
1c message is legal and (ii) it is the only 2a message that the leader
sends.  In the BPCon algorithm, there are no explicit 2a messages.
They are implicitly sent by the acceptors when they send enough 2av
messages.

We leave unspecified how an acceptor discovers what 1b messages have
been sent.  In the Castro-Liskov algorithm, this is done by having
acceptors relay messages sent by other acceptors.  An acceptor knows
that a 1b message has been sent if it receives it directly or else
receives a copy from a weak Byzantine quorum of acceptors.  A
(non-malicious) leader must determine what 1b messages acceptors know
about so it chooses a value so that a quorum of acceptors will act on
its Phase1c message and cause that value to be chosen.  However, this
is necessary only for liveness, so we ignore this for now.

In other implementations of our algorithm, the leader sends along with
the 1c message a proof that the necessary 1b messages have been sent.
The easiest way to do this is to have acceptors digitally sign their 1b
messages, so a copy of the message proves that it has been sent (by the
acceptor indicated in the message's acc field).  The necessary proofs
can also be constructed using only message authenticators (like the
ones used in the Castro-Liskov algorithm); how this is done is
described elsewhere.

In the abstract algorithm presented here, which we call
BPCon, we do not specify how acceptors learn what 1b
messages have been sent.  We simply introduce a variable knowsSent such
that knowsSent[a] represents the set of 1b messages that (good)
acceptor a knows have been sent, and have an action that
nondeterministically adds sent 1b messages to this set.

--algorithm BPCon {
  (**************************************************************************
The variables:

    maxBal[a]  = Highest ballot in which acceptor a has participated.

    maxVBal[a] = Highest ballot in which acceptor a has cast a vote
                 (sent a 2b message); or -1 if it hasn't cast a vote.

    maxVVal[a] = Value acceptor a has voted for in ballot maxVBal[a],
                  or None if maxVBal[a] = -1.

    2avSent[a] = A set of records in [val : Value, bal : Ballot]
                 describing the 2av messages that a has sent.  A
                 record is added to this set, and any element with
                 the same val field (and lower bal field) removed
                 when a sends a 2av message.

    knownSent[a] = The set of 1b messages that acceptor a knows have
                   been sent.

    bmsgs = The set of all messages that have been sent.  See the
            discussion of the msgs variable in module PConProof
            to understand our modeling of message passing.
  **************************************************************************)
  variables maxBal  = [a \in Acceptor |-> -1],
            maxVBal = [a \in Acceptor |-> -1] ,
            maxVVal = [a \in Acceptor |-> None] ,
            2avSent = [a \in Acceptor |-> {}],
            knowsSent = [a \in Acceptor |-> {}],
            bmsgs = {}
  define {
    sentMsgs(type, bal) == {m \in bmsgs: m.type = type /\ m.bal = bal}

    KnowsSafeAt(ac, b, v) ==
      (*********************************************************************)
      (* True for an acceptor ac, ballot b, and value v iff the set of 1b  *)
      (* messages in knowsSent[ac] implies that value v is safe at ballot  *)
      (* b in the PaxosConsensus algorithm being emulated by the good      *)
      (* acceptors.  To understand the definition, see the definition of   *)
      (* ShowsSafeAt in module PConProof and recall (a) the meaning of the *)
      (* mCBal and mCVal fields of a 1b message and (b) that the set of    *)
      (* real acceptors in a ByzQuorum forms a quorum of the               *)
      (* PaxosConsensus algorithm.                                         *)
      (*********************************************************************)
      LET S == {m \in knowsSent[ac] : m.bal = b}
      IN  \/ \E BQ \in ByzQuorum :
               \A a \in BQ : \E m \in S : /\ m.acc = a
                                          /\ m.mbal = -1
          \/ \E c \in 0..(b-1):
               /\ \E BQ \in ByzQuorum :
                    \A a \in BQ : \E m \in S : /\ m.acc = a
                                               /\ m.mbal =< c
                                               /\ (m.mbal = c) => (m.mval = v)
               /\ \E WQ \in WeakQuorum :
                    \A a \in WQ :
                      \E m \in S : /\ m.acc = a
                                   /\ \E r \in m.m2av : /\ r.bal >= c
                                                        /\ r.val = v
   }

  (*************************************************************************)
  (* We now describe the processes' actions as macros.                     *)
  (*                                                                       *)
  (* The following two macros send a message and a set of messages,        *)
  (* respectively.  These macros are so simple that they're hardly worth   *)
  (* introducing, but they do make the processes a little easier to read.  *)
  (*************************************************************************)
  macro SendMessage(m) { bmsgs := bmsgs \cup {m} }
  macro SendSetOfMessages(S) { bmsgs := bmsgs \cup S }

  (*************************************************************************)
  (* As in the Paxos consensus algorithm, a ballot `self' leader (good or  *)
  (* malicious) can execute a Phase1a ation at any time.                   *)
  (*************************************************************************)
  macro Phase1a() { SendMessage([type |-> "1a", bal |-> self]) }

  (*************************************************************************)
  (* The acceptor's Phase1b ation is similar to that of the PaxosConsensus *)
  (* algorithm.                                                            *)
  (*************************************************************************)
  macro Phase1b(b) {
   when (b > maxBal[self]) /\ (sentMsgs("1a", b) # {}) ;
   maxBal[self] := b ;
   SendMessage([type |-> "1b", bal |-> b, acc |-> self, m2av |-> 2avSent[self],
                mbal |-> maxVBal[self], mval |-> maxVVal[self]])
   }

  (*************************************************************************)
  (* A good ballot `self' leader can send a phase 1c message for value v   *)
  (* if it knows that the messages in knowsSent[a] for a Quorum of (good)  *)
  (* acceptors imply that they know that v is safe at ballot `self', and   *)
  (* that they can convince any other acceptor that the appropriate 1b     *)
  (* messages have been sent to that it will also know that v is safe at   *)
  (* ballot `self'.                                                        *)
  (*                                                                       *)
  (* A malicious ballot `self' leader can send any phase 1c messages it    *)
  (* wants (including one that a good leader could send).  We prove safety *)
  (* with a Phase1c ation that allows a leader to be malicious.  To prove  *)
  (* liveness, we will have to assume a good leader that sends only        *)
  (* correct 1c messages.                                                  *)
  (*                                                                       *)
  (* As in the PaxosConsensus algorithm, we allow a Phase1c action to send *)
  (* a set of Phase1c messages.  (This is not done in the Castro-Liskov    *)
  (* algorithm, but seems natural in light of the PaxosConsensus           *)
  (* algorithm.)                                                           *)
  (*************************************************************************)
  macro Phase1c() {
    with (S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]) {
      SendSetOfMessages(S) }
   }

  (*************************************************************************)
  (* If acceptor `self' receives a ballot b phase 1c message with value v, *)
  (* it relays v in a phase 2av message if                                 *)
  (*                                                                       *)
  (*   - it has not already sent a 2av message in this or a later          *)
  (*     ballot and                                                        *)
  (*                                                                       *)
  (*   - the messages in knowsSent[self] show it that v is safe at b in    *)
  (*     the non-Byzantine Paxos consensus algorithm being emulated.       *)
  (*************************************************************************)
  macro Phase2av(b) {
    when /\ maxBal[self] =< b
         /\ \A r \in 2avSent[self] : r.bal < b ;
            \* We could just as well have used r.bal # b in this condition.
    with (m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}) {
       SendMessage([type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]) ;
       2avSent[self] :=  {r \in 2avSent[self] : r.val # m.val}
                           \cup {[val |-> m.val, bal |-> b]}
      } ;
    maxBal[self]  := b ;
   }

  (*************************************************************************)
  (* Acceptor `self' can send a phase 2b message with value v if it has    *)
  (* received phase 2av messages from a Byzantine quorum, which implies    *)
  (* that a quorum of good acceptors assert that this is the first 1c      *)
  (* message sent by the leader and that the leader was allowed to send    *)
  (* that message.  It sets maxBal[self], maxVBal[self], and maxVVal[self] *)
  (* as in the non-Byzantine algorithm.                                    *)
  (*************************************************************************)
  macro Phase2b(b) {
    when maxBal[self] =< b ;
    with (v \in {vv \in Value :
                   \E Q \in ByzQuorum :
                      \A aa \in Q :
                         \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                       /\ m.acc = aa} ) {
        SendMessage([type |-> "2b", acc |-> self, bal |-> b, val |-> v]) ;
        maxVVal[self] := v ;
      } ;
    maxBal[self] := b ;
    maxVBal[self] := b
   }

  (*************************************************************************)
  (* At any time, an acceptor can learn that some set of 1b messages were  *)
  (* sent (but only if they atually were sent).                            *)
  (*************************************************************************)
  macro LearnsSent(b) {
    with (S \in SUBSET sentMsgs("1b", b)) {
       knowsSent[self] := knowsSent[self] \cup S
     }
   }
  (*************************************************************************)
  (* A malicious acceptor `self' can send any acceptor message indicating  *)
  (* that it is from itself.  Since a malicious acceptor could allow other *)
  (* malicious processes to forge its messages, this action could          *)
  (* represent the sending of the message by any malicious process.        *)
  (*************************************************************************)
  macro FakingAcceptor() {
    with ( m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage :
                   mm.acc = self} ) {
         SendMessage(m)
     }
   }

  (*************************************************************************)
  (* We combine these individual actions into a complete algorithm in the  *)
  (* usual way, with separate process declarations for the acceptor,       *)
  (* leader, and fake acceptor processes.                                  *)
  (*************************************************************************)
  process (acceptor \in Acceptor) {
    acc: while (TRUE) {
           with (b \in Ballot) {either Phase1b(b) or Phase2av(b)
                                  or Phase2b(b) or LearnsSent(b)}
    }
   }

  process (leader \in Ballot) {
    ldr: while (TRUE) {
          either Phase1a() or Phase1c()
         }
   }

  process (facceptor \in FakeAcceptor) {
     facc : while (TRUE) { FakingAcceptor() }
   }
}

Below is the TLA+ translation, as produced by the translator.  (Some
blank lines have been removed.)
**************************************************************************)
\* BEGIN TRANSLATION
VARIABLES maxBal, maxVBal, maxVVal, 2avSent, knowsSent, bmsgs

(* define statement *)
sentMsgs(type, bal) == {m \in bmsgs: m.type = type /\ m.bal = bal}

KnowsSafeAt(ac, b, v) ==
  LET S == {m \in knowsSent[ac] : m.bal = b}
  IN  \/ \E BQ \in ByzQuorum :
           \A a \in BQ : \E m \in S : /\ m.acc = a
                                      /\ m.mbal = -1
      \/ \E c \in 0..(b-1):
           /\ \E BQ \in ByzQuorum :
                \A a \in BQ : \E m \in S : /\ m.acc = a
                                           /\ m.mbal =< c
                                           /\ (m.mbal = c) => (m.mval = v)
           /\ \E WQ \in WeakQuorum :
                \A a \in WQ :
                  \E m \in S : /\ m.acc = a
                               /\ \E r \in m.m2av : /\ r.bal >= c
                                                    /\ r.val = v


vars == << maxBal, maxVBal, maxVVal, 2avSent, knowsSent, bmsgs >>

ProcSet == (Acceptor) \cup (Ballot) \cup (FakeAcceptor)

Init == (* Global variables *)
        /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVVal = [a \in Acceptor |-> None]
        /\ 2avSent = [a \in Acceptor |-> {}]
        /\ knowsSent = [a \in Acceptor |-> {}]
        /\ bmsgs = {}

acceptor(self) == \E b \in Ballot:
                    \/ /\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ bmsgs' = (bmsgs \cup {([type |-> "1b", bal |-> b, acc |-> self, m2av |-> 2avSent[self],
                                                  mbal |-> maxVBal[self], mval |-> maxVVal[self]])})
                       /\ UNCHANGED <<maxVBal, maxVVal, 2avSent, knowsSent>>
                    \/ /\ /\ maxBal[self] =< b
                          /\ \A r \in 2avSent[self] : r.bal < b
                       /\ \E m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}:
                            /\ bmsgs' = (bmsgs \cup {([type |-> "2av", bal |-> b, val |-> m.val, acc |-> self])})
                            /\ 2avSent' = [2avSent EXCEPT ![self] = {r \in 2avSent[self] : r.val # m.val}
                                                                      \cup {[val |-> m.val, bal |-> b]}]
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ UNCHANGED <<maxVBal, maxVVal, knowsSent>>
                    \/ /\ maxBal[self] =< b
                       /\ \E v \in {vv \in Value :
                                      \E Q \in ByzQuorum :
                                         \A aa \in Q :
                                            \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                                          /\ m.acc = aa}:
                            /\ bmsgs' = (bmsgs \cup {([type |-> "2b", acc |-> self, bal |-> b, val |-> v])})
                            /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
                       /\ UNCHANGED <<2avSent, knowsSent>>
                    \/ /\ \E S \in SUBSET sentMsgs("1b", b):
                            knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
                       /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, bmsgs>>


leader(self) == /\ \/ /\ bmsgs' = (bmsgs \cup {([type |-> "1a", bal |-> self])})
                   \/ /\ \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
                           bmsgs' = (bmsgs \cup S)
                /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>


facceptor(self) == /\ \E m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage :
                                 mm.acc = self}:
                        bmsgs' = (bmsgs \cup {m})
                   /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent,
                                   knowsSent >>


Next == (\E self \in Acceptor: acceptor(self))
           \/ (\E self \in Ballot: leader(self))
           \/ (\E self \in FakeAcceptor: facceptor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* As in module PConProof, we now rewrite the next-state relation in a     *)
(* form more convenient for writing proofs.                                *)
(***************************************************************************)
Phase1b(self, b) ==
  /\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ bmsgs' = bmsgs \cup {[type  |-> "1b", bal |-> b, acc |-> self,
                           m2av |-> 2avSent[self],
                           mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
  /\ UNCHANGED <<maxVBal, maxVVal, 2avSent, knowsSent>>

Phase2av(self, b) ==
  /\ maxBal[self] =< b
  /\ \A r \in 2avSent[self] : r.bal < b
  /\ \E m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}:
       /\ bmsgs' = bmsgs \cup
                    {[type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]}
       /\ 2avSent' = [2avSent EXCEPT
                        ![self] = {r \in 2avSent[self] : r.val # m.val}
                                    \cup {[val |-> m.val, bal |-> b]}]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ UNCHANGED <<maxVBal, maxVVal, knowsSent>>

Phase2b(self, b) ==
  /\ maxBal[self] =< b
  /\ \E v \in {vv \in Value :
                 \E Q \in ByzQuorum :
                    \A a \in Q :
                       \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                     /\ m.acc = a }:
       /\ bmsgs' = (bmsgs \cup
                     {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]})
       /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
  /\ UNCHANGED <<2avSent, knowsSent>>

LearnsSent(self, b) ==
 /\ \E S \in SUBSET sentMsgs("1b", b):
       knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
 /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, bmsgs>>

Phase1a(self) ==
  /\ bmsgs' = (bmsgs \cup {[type |-> "1a", bal |-> self]})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

Phase1c(self) ==
  /\ \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
                        bmsgs' = (bmsgs \cup S)
  /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

FakingAcceptor(self) ==
  /\ \E m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage : mm.acc = self} :
         bmsgs' = (bmsgs \cup {m})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma describes how the next-state relation Next can be   *)
(* written in terms of the actions defined above.                          *)
(***************************************************************************)
LEMMA NextDef ==
 Next = \/ \E self \in Acceptor :
             \E b \in Ballot : \/ Phase1b(self, b)
                               \/ Phase2av(self, b)
                               \/ Phase2b(self,b)
                               \/ LearnsSent(self, b)
        \/ \E self \in Ballot : \/ Phase1a(self)
                                \/ Phase1c(self)
        \/ \E self \in FakeAcceptor : FakingAcceptor(self)
<1>1. \A self : acceptor(self) = NextDef!2!1!(self)
  BY  DEF acceptor, Phase1b,  Phase2av, Phase2b, LearnsSent
<1>2. \A self : leader(self) = NextDef!2!2!(self)
  BY DEF leader, Phase1a, Phase1c
<1>3. \A self : facceptor(self) = NextDef!2!3!(self)
  BY DEF facceptor, FakingAcceptor
<1>4. QED
      BY <1>1, <1>2, <1>3
      DEF Next, acceptor, leader, facceptor
-----------------------------------------------------------------------------
(***************************************************************************)
(*                        THE REFINEMENT MAPPING                           *)
(***************************************************************************)

(***************************************************************************)
(* We define a quorum to be the set of acceptors in a Byzantine quorum.    *)
(* The quorum assumption QA of module PConProof, which we here call        *)
(* QuorumTheorem, follows easily from the definition and assumption BQA.   *)
(***************************************************************************)
Quorum == {S \cap Acceptor : S \in ByzQuorum}

THEOREM QuorumTheorem ==
         /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
         /\ \A Q \in Quorum : Q \subseteq Acceptor
<1>1. QuorumTheorem!1
  <2>1. SUFFICES ASSUME NEW Q1 \in Quorum, NEW Q2 \in Quorum
                 PROVE Q1 \cap Q2 # {}
    OBVIOUS
  <2>2. PICK BQ1 \in ByzQuorum, BQ2 \in ByzQuorum :
               /\ Q1 = BQ1 \cap Acceptor
               /\ Q2 = BQ2 \cap Acceptor
     BY <2>1 DEF Quorum
  <2>3. Q1 \cap Q2 = BQ1 \cap BQ2 \cap Acceptor
    BY <2>2
  <2>4. QED
    BY BQA, <2>3
<1>2. QuorumTheorem!2
  BY DEF Quorum
<1>3. QED
  BY <1>1, <1>2

(***************************************************************************)
(* We now define refinement mapping under which our algorithm implements   *)
(* the algorithm of module PConProof.  First, we define the set msgs that  *)
(* implements the variable of the same name in PConProof.  There are two   *)
(* non-obvious parts of the definition.                                    *)
(*                                                                         *)
(* 1.  The 1c messages in msgs should just be the ones that are            *)
(* legal--that is, messages whose value is safe at the indicated ballot.   *)
(* The obvious way to define legality is in terms of 1b messages that have *)
(* been sent.  However, this has the effect that sending a 1b message can  *)
(* add both that 1b message and one or more 1c messages to msgs.  Proving  *)
(* implementation under this refinement mapping would require adding a     *)
(* stuttering variable.  Instead, we define the 1c message to be legal if  *)
(* the set of 1b messages that some acceptor knows were sent confirms its  *)
(* legality.  Thus, those 1c messages are added to msgs by the LearnsSent  *)
(* ation, which has no other effect on the refinement mapping.             *)
(*                                                                         *)
(* 2.  A 2a message is added to msgs when a quorum of acceptors have       *)
(* reacted to it by sending a 2av message.                                 *)
(***************************************************************************)
msgsOfType(t) == {m \in bmsgs : m.type = t }

acceptorMsgsOfType(t) == {m \in msgsOfType(t) : m.acc \in  Acceptor}

1bRestrict(m) == [type |-> "1b", acc |-> m.acc, bal |-> m.bal,
                  mbal |-> m.mbal, mval |-> m.mval]

1bmsgs == { 1bRestrict(m) : m \in acceptorMsgsOfType("1b") }

1cmsgs == {m \in msgsOfType("1c") :
                   \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)}

2amsgs == {m \in [type : {"2a"}, bal : Ballot, val : Value] :
             \E Q \in Quorum :
               \A a \in Q :
                 \E m2av \in acceptorMsgsOfType("2av") :
                    /\ m2av.acc = a
                    /\ m2av.bal = m.bal
                    /\ m2av.val = m.val }

msgs == msgsOfType("1a") \cup 1bmsgs \cup 1cmsgs \cup 2amsgs
         \cup acceptorMsgsOfType("2b")

(***************************************************************************)
(* We now define PmaxBal, the state function with which we instantiate the *)
(* variable maxBal of PConProof.  The reason we don't just instantiate it  *)
(* with the variable maxBal is that maxBal[a] can change when acceptor `a' *)
(* performs a Phase2av ation, which does not correspond to any acceptor    *)
(* action of the PCon algorithm.  We want PmaxBal[a] to change only        *)
(* when `a' performs a Phase1b or Phase2b ation--that is, when it sends a  *)
(* 1b or 2b message.  Thus, we define PmaxBal[a] to be the largest bal     *)
(* field of all 1b and 2b messages sent by `a'.                            *)
(*                                                                         *)
(* To define PmaxBal, we need to define an operator MaxBallot so that      *)
(* MaxBallot(S) is the largest element of S if S is non-empty a finite set *)
(* consisting of ballot numbers and possibly the value -1.                 *)
(***************************************************************************)
MaxBallot(S) ==
  IF S = {} THEN -1
            ELSE CHOOSE mb \in S : \A x \in S : mb  >= x

(***************************************************************************)
(* To prove that the CHOOSE in this definition actually does choose a      *)
(* maximum of S when S is nonempty, we need the following trivial fact.    *)
(* It has been checked by TLC with -5..5 substituted for Int.              *)
(***************************************************************************)
AXIOM FiniteSetHasMax ==
        \A S \in SUBSET Int :
          IsFiniteSet(S) /\ (S # {}) => \E max \in S : \A x \in S : max >= x

(***************************************************************************)
(* Our proofs use this property of MaxBallot.                              *)
(***************************************************************************)
THEOREM MaxBallotProp  ==
         \A S \in SUBSET (Ballot \cup {-1}) :
            IsFiniteSet(S) =>
              IF S = {} THEN MaxBallot(S) = -1
                        ELSE /\ MaxBallot(S) \in S
                             /\ \A x \in S : MaxBallot(S) >= x
<1> SUFFICES ASSUME NEW S \in SUBSET (Ballot \cup {-1}),
                    IsFiniteSet(S)
             PROVE  MaxBallotProp!(S)!2
  OBVIOUS
<1>1. CASE S = {}
  BY <1>1 DEF MaxBallot
<1>2. CASE S # {}
  <2>1. S \in SUBSET Int
    BY DEF Ballot \* <2>1
  <2>2. \E mb \in S : \A x \in S : mb >= x
    BY <2>1, <1>2,  FiniteSetHasMax

  <2>3. QED
    BY <1>2, <2>2 DEF MaxBallot
<1>3. QED
  BY <1>1, <1>2

(***************************************************************************)
(* We now prove a couple of lemmas about MaxBallot.                        *)
(***************************************************************************)
LEMMA MaxBallotLemma1 ==
          \A S \in SUBSET (Ballot \cup {-1}) :
            IsFiniteSet(S) =>
              \A y \in S :
               (\A x \in S : y >= x) => (y = MaxBallot(S))
<1>1. SUFFICES ASSUME NEW S \in SUBSET (Ballot \cup {-1}),
                      IsFiniteSet(S),
                      NEW y \in S,
                      \A x \in S : y >= x
               PROVE  y = MaxBallot(S)
  OBVIOUS
<1>2. /\ MaxBallot(S) \in S
      /\ \A x \in S : MaxBallot(S) >= x
  BY <1>1, MaxBallotProp
<1>3. MaxBallot(S) >= y
  BY  <1>2
<1>4. y \in Ballot \cup {-1}
  OBVIOUS
<1>5 y >= MaxBallot(S)
  BY <1>1, <1>2
<1>6. \A mbs \in Ballot \cup {-1} :
          mbs >= y /\ y >= mbs => y = mbs
  BY <1>4, SimpleArithmetic DEF Ballot
<1>7. MaxBallot(S) \in Ballot \cup {-1}
  BY <1>2
<1>8. QED
  BY <1>3, <1>5, <1>6, <1>7

LEMMA MaxBallotLemma2 ==
         \A S, T \in SUBSET (Ballot \cup {-1}) :
            IsFiniteSet(S) /\ IsFiniteSet(T) =>
              MaxBallot(S \cup T) = IF MaxBallot(S) >= MaxBallot(T)
                                      THEN MaxBallot(S)
                                      ELSE MaxBallot(T)
<1>1. \A S \in SUBSET (Ballot \cup {-1}) :
         IsFiniteSet(S) => (MaxBallot(S) \in Ballot \cup {-1})
  BY MaxBallotProp
<1>2. ASSUME NEW S \in SUBSET (Ballot \cup {-1}),
             NEW T \in SUBSET (Ballot \cup {-1}),
             IsFiniteSet(S) /\ IsFiniteSet(T),
             MaxBallot(S) >= MaxBallot(T)
      PROVE  MaxBallot(S \cup T) = MaxBallot(S)
  <2>1. CASE S = {}
    <3>1. CASE T = {}
      BY <3>1
    <3>2. CASE T # {}
      <4>1. MaxBallot(S) = -1
        BY <1>2, <2>1, MaxBallotProp
      <4>2. MaxBallot(T) = -1
        <5>1. \A x \in Ballot \cup {-1} : -1 >= x => x = -1
          BY SimpleArithmetic DEF Ballot
        <5>2. MaxBallot(T) \in Ballot \cup {-1}
          BY  <1>2, <1>1
        <5>3. QED
          BY <5>1, <5>2, <4>1, <1>2
      <4>3. -1 \in T /\ \A x \in T : -1 >= x
        BY <4>2, <3>2, <1>2, MaxBallotProp
      <4>4. QED
        BY <4>1, <4>3, <3>2, <2>1, <1>2, MaxBallotLemma1
    <3>3. QED
      BY <3>1, <3>2
  <2>2. CASE S # {}
    <3>1. CASE T = {}
      BY <3>1
    <3>2. CASE T # {}
      <4>1. /\ MaxBallot(S) \in S
            /\ \A x \in S : MaxBallot(S) >= x
        BY <2>2, <1>2, MaxBallotProp
      <4>2. /\ MaxBallot(T) \in T
            /\ \A x \in T : MaxBallot(T) >= x
        BY <3>2, <1>2, MaxBallotProp
      <4>3. \A x, y \in Ballot \cup {-1}, TT \in SUBSET (Ballot \cup {-1}) :
               (x >= y) /\ (\A z \in TT : y >= z) => (\A z \in TT : x >= z)
        <5>1. SUFFICES ASSUME NEW x \in Ballot \cup {-1}, NEW y \in Ballot \cup {-1},
                              NEW TT \in SUBSET (Ballot \cup {-1}),
                              (x >= y), \A z \in TT : y >= z
                       PROVE   (\A z \in TT : x >= z)
          OBVIOUS
        <5>2. SUFFICES ASSUME NEW z \in TT
                       PROVE  x >= z
          OBVIOUS
        <5>3. z \in Ballot \cup {-1}
          BY <5>1, <5>2
        <5>4. y >= z
          BY <5>1
        <5>5. QED
          BY SimpleArithmetic, <5>1, <5>3, <5>4 DEF Ballot

      <4>4. /\ MaxBallot(S) \in Ballot \cup {-1}
            /\ MaxBallot(T) \in Ballot \cup {-1}
        BY <1>1, <1>2
      <4>5. \A x \in T : MaxBallot(S) >= x
        BY <1>2, <4>2, <4>3,  <4>4
      <4>6. /\ MaxBallot(S) \in S \cup T
            /\ \A x \in S \cup T : MaxBallot(S) >= x
        BY <4>1, <4>5
      <4>7. IsFiniteSet(S \cup T)
        BY <1>2, UnionOfFiniteSetsFinite
      <4>8. QED
        BY <4>6, <4>7, MaxBallotLemma1
    <3>3. QED
      BY <3>1, <3>2
  <2>3. QED
    BY <2>1, <2>2
<1>3. SUFFICES ASSUME NEW S \in SUBSET (Ballot \cup {-1}),
                      NEW T \in SUBSET (Ballot \cup {-1}),
                      IsFiniteSet(S) /\ IsFiniteSet(T)
               PROVE  MaxBallot(S \cup T) = IF MaxBallot(S) >= MaxBallot(T)
                                              THEN MaxBallot(S)
                                              ELSE MaxBallot(T)
  OBVIOUS
<1>4. CASE MaxBallot(S) >= MaxBallot(T)
  <2> SUFFICES  MaxBallot(S \cup T) = MaxBallot(S)
   BY <1>3, <1>4
  <2> QED
    BY <1>2, <1>3, <1>4 \* added <1>3 on 13 Nov 2010
<1>5. CASE ~ (MaxBallot(S) >= MaxBallot(T))
  <2> SUFFICES MaxBallot(T \cup S) = MaxBallot(T)
    BY <1>3, <1>5
  <2> MaxBallot(T) >= MaxBallot(S)
    <3>1. \A x, y \in  Ballot \cup {-1} : x >= y \/ y >= x
      BY SimpleArithmetic DEF Ballot
    <3>2. /\ MaxBallot(S) \in Ballot \cup {-1}
          /\ MaxBallot(T) \in Ballot \cup {-1}
      BY <1>1, <1>3
    <3>3. QED
      BY <1>5, <3>1, <3>2
  <2> QED
    BY <1>2, <1>3, <1>5
<1>6. QED
  BY  <1>4, <1>5


(***************************************************************************)
(* We finally come to our definition of PmaxBal, the state function        *)
(* substituted for variable maxBal of module PConProof by our refinement   *)
(* mapping.  We also prove a couple of lemmas about PmaxBal.               *)
(***************************************************************************)

1bOr2bMsgs == {m \in bmsgs : m.type \in {"1b", "2b"}}

PmaxBal == [a \in Acceptor |->
              MaxBallot({m.bal : m \in {ma \in 1bOr2bMsgs :
                                           ma.acc = a}})]

LEMMA PmaxBalLemma1 ==
         \A m : /\ bmsgs' = bmsgs \cup {m}
                /\ m.type # "1b" /\ m.type # "2b"
                => PmaxBal' = PmaxBal
<1> SUFFICES ASSUME NEW m ,
                    bmsgs' = bmsgs \cup {m},
                    m.type # "1b" /\ m.type # "2b"
             PROVE  PmaxBal' = PmaxBal
  OBVIOUS
<1>1. ASSUME NEW ma, ma.type \in {"1b", "2b"}
      PROVE ma \in bmsgs' <=> ma \in bmsgs
  BY <1>1
<1>2. QED
  BY <1>1 DEF PmaxBal, 1bOr2bMsgs

LEMMA PmaxBalLemma2 ==
        \A m : (bmsgs' = bmsgs \cup {m}) =>
            \A a \in Acceptor : (m.acc # a => PmaxBal'[a] = PmaxBal[a])
<1> SUFFICES ASSUME NEW m,
                    bmsgs' = bmsgs \cup {m},
                    NEW a \in Acceptor,
                    m.acc # a
             PROVE  PmaxBal'[a] = PmaxBal[a]
  OBVIOUS
<1>1. ASSUME NEW ma, ma.acc # m.acc
      PROVE ma \in bmsgs' <=> ma \in bmsgs
  BY <1>1
<1>2. QED
  BY <1>1 DEF PmaxBal, 1bOr2bMsgs

(***************************************************************************)
(* Finally, we define the refinement mapping.  As before, for any operator *)
(* op defined in module PConProof, the following INSTANCE statement        *)
(* defines P!op to be the operator obtained from op by the indicated       *)
(* substitutions, along with the implicit substitutions                    *)
(*                                                                         *)
(*     Acceptor <- Acceptor,                                               *)
(*     Quorum   <- Quorum                                                  *)
(*     Value    <- Value                                                   *)
(*     maxVBal  <- maxVBal                                                 *)
(*     maxVVal  <- maxVVal                                                 *)
(*     msgs     <- msgs                                                    *)
(***************************************************************************)
P == INSTANCE PConProof WITH maxBal <- PmaxBal
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the inductive invariant Inv used in our proof.  It is     *)
(* defined to be the conjunction of a number of separate invariants that   *)
(* we define first, starting with the ever-present type-correctness        *)
(* invariant.                                                              *)
(***************************************************************************)
TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ 2avSent \in [Acceptor -> SUBSET [val : Value, bal : Ballot]]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVVal \in [Acceptor -> Value \cup {None}]
          /\ knowsSent \in [Acceptor -> SUBSET 1bMessage]
          /\ bmsgs \subseteq BMessage

(***************************************************************************)
(* To use the definition of PmaxBal, we need to know that the set of 1b    *)
(* and 2b messages in bmsgs is finite.  This is asserted by the following  *)
(* invariant.  Note that the set bmsgs is not necessarily finite because   *)
(* we allow a Phase1c action to send an infinite number of 1c messages.    *)
(***************************************************************************)
bmsgsFinite == IsFiniteSet(1bOr2bMsgs)

(***************************************************************************)
(* The following lemma is used to prove the invariance of bmsgsFinite.     *)
(***************************************************************************)
LEMMA FiniteMsgsLemma ==
        \A m : bmsgsFinite /\ (bmsgs' = bmsgs \cup {m}) => bmsgsFinite'
<1> SUFFICES ASSUME NEW m, bmsgsFinite, bmsgs' = bmsgs \cup {m}
             PROVE  bmsgsFinite'
  OBVIOUS
<1>1. CASE (m.type \in {"1b", "2b"})
  <2>1. 1bOr2bMsgs' = 1bOr2bMsgs \cup {m}
    BY <1>1 DEF 1bOr2bMsgs
  <2>2. QED
    BY <2>1, SingletonSetFinite, UnionOfFiniteSetsFinite DEF bmsgsFinite
<1>2. CASE m.type \notin {"1b", "2b"}
  BY <1>2 DEF bmsgsFinite, 1bOr2bMsgs
<1>3. QED
  BY <1>1, <1>2

(***************************************************************************)
(* Invariant 1bInv1 asserts that if (good) acceptor `a' has mCBal[a] # -1, *)
(* then there is a 1c message for ballot mCBal[a] and value mCVal[a] in    *)
(* the emulated execution of algorithm PCon.                               *)
(***************************************************************************)
1bInv1 == \A m \in bmsgs  :
             /\ m.type = "1b"
             /\ m.acc \in Acceptor
             => \A r \in m.m2av :
                [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs

(***************************************************************************)
(* Invariant 1bInv2 asserts that an acceptor sends at most one 1b message  *)
(* for any ballot.                                                         *)
(***************************************************************************)
1bInv2 == \A m1, m2 \in bmsgs  :
             /\ m1.type = "1b"
             /\ m2.type = "1b"
             /\ m1.acc \in Acceptor
             /\ m1.acc = m2.acc
             /\ m1.bal = m2.bal
             => m1 = m2

(***************************************************************************)
(* Invariant 2avInv1 asserts that an acceptor sends at most one 2av        *)
(* message in any ballot.                                                  *)
(***************************************************************************)
2avInv1 == \A m1, m2 \in bmsgs :
             /\ m1.type = "2av"
             /\ m2.type = "2av"
             /\ m1.acc \in Acceptor
             /\ m1.acc = m2.acc
             /\ m1.bal = m2.bal
             => m1 = m2

(***************************************************************************)
(* Invariant 2avInv2 follows easily from the meaning (and setting) of      *)
(* 2avSent.                                                                *)
(***************************************************************************)
2avInv2 == \A m \in bmsgs :
             /\ m.type = "2av"
             /\ m.acc \in Acceptor
             => \E r \in 2avSent[m.acc] : /\ r.val = m.val
                                          /\ r.bal >= m.bal

(***************************************************************************)
(* Invariant 2avInv3 asserts that an acceptor sends a 2av message only if  *)
(* the required 1c message exists in the emulated execution of             *)
(* algorithm PConf.                                                        *)
(***************************************************************************)
2avInv3 == \A m \in bmsgs :
             /\ m.type = "2av"
             /\ m.acc \in Acceptor
             => [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs

(***************************************************************************)
(* Invariant maxBalInv is a simple consequence of the fact that an         *)
(* acceptor `a' sets maxBal[a] to b whenever it sends a 1b, 2av, or 2b     *)
(* message in ballot b.                                                    *)
(***************************************************************************)
maxBalInv == \A m \in bmsgs :
               /\ m.type \in {"1b", "2av", "2b"}
               /\ m.acc \in Acceptor
               => m.bal =< maxBal[m.acc]

(***************************************************************************)
(* Invariant accInv asserts some simple relations between the variables    *)
(* local to an acceptor, as well as the fact that acceptor `a' sets        *)
(* maxCBal[a] to b and maxCVal[a] to v only if there is a ballot-b 1c      *)
(* message for value c in the simulated execution of the PCon              *)
(* algorithm.                                                              *)
(***************************************************************************)
accInv == \A a \in Acceptor :
            \A r \in 2avSent[a] :
              /\ r.bal =< maxBal[a]
              /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs

(***************************************************************************)
(* Invariant knowsSentInv simply asserts that for any acceptor `a',        *)
(* knowsSent[a] is a set of 1b messages that have actually been sent.      *)
(***************************************************************************)
knowsSentInv == \A a \in Acceptor : knowsSent[a] \subseteq msgsOfType("1b")

Inv ==
 TypeOK /\ bmsgsFinite /\ 1bInv1 /\ 1bInv2 /\ maxBalInv  /\ 2avInv1 /\ 2avInv2
   /\ 2avInv3 /\ accInv /\ knowsSentInv
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now prove some simple lemmas that are useful for reasoning about     *)
(* PmaxBal.                                                                *)
(***************************************************************************)
LEMMA PMaxBalLemma3 ==
        ASSUME TypeOK,
               bmsgsFinite,
               NEW a \in Acceptor
        PROVE  LET S == {m.bal : m \in {ma \in bmsgs :
                                           /\ ma.type \in {"1b", "2b"}
                                           /\ ma.acc = a}}
               IN  /\ IsFiniteSet(S)
                   /\ S \in SUBSET Ballot
<1> DEFINE T == {ma \in bmsgs : /\ ma.type \in {"1b", "2b"}
                                /\ ma.acc = a}
           S == {m.bal : m \in T}
<1>1. IsFiniteSet(S)
  <2>1. IsFiniteSet(T)
    BY SubsetOfFiniteSetFinite DEF bmsgsFinite, 1bOr2bMsgs
  <2> DEFINE f[m \in T] == m.bal
  <2>2. IsFiniteSet({f[m] : m \in T})
    BY <2>1, ImageOfFiniteSetFinite
  <2>3. QED
    BY <2>2
<1>2. ASSUME NEW b \in S
      PROVE  b \in Ballot
  <2>1. PICK m \in bmsgs : b = m.bal /\ m.type \in {"1b", "2b"}
    OBVIOUS
  <2>2. CASE m.type = "1b"
    <3>1. m \in 1bMessage
      BY <2>2,  BMessageLemma DEF TypeOK
    <3>2. QED
      BY <3>1, <2>1 DEF 1bMessage
  <2>3. CASE m.type = "2b"
    <3>1. m \in 2bMessage
      BY <2>3,  BMessageLemma DEF TypeOK
    <3>2. QED
      BY <3>1, <2>1 DEF 2bMessage
  <2>4. QED
    BY <2>1, <2>2, <2>3
<1>3. QED
  BY <1>1, <1>2

LEMMA PmaxBalLemma4 ==
         TypeOK /\ maxBalInv /\ bmsgsFinite =>
             \A a \in Acceptor : PmaxBal[a] =< maxBal[a]
<1> SUFFICES ASSUME TypeOK,
                    maxBalInv,
                    bmsgsFinite,
                    NEW a \in Acceptor
             PROVE  PmaxBal[a] =< maxBal[a]
  OBVIOUS
<1> DEFINE SM == {ma \in bmsgs : /\ ma.type \in {"1b", "2b"}
                                 /\ ma.acc = a}
           S  == {ma.bal : ma \in SM}
<1>1. PmaxBal[a] = MaxBallot(S)
  BY DEF PmaxBal, 1bOr2bMsgs
<1>2. /\ IsFiniteSet(S)
      /\ S \in SUBSET (Ballot \cup {-1})
  BY PMaxBalLemma3
<1>3. \A b \in S : b =< maxBal[a]
  BY DEF maxBalInv
<1>4. CASE S = {}
  <2>1. PmaxBal[a] = -1
    BY <1>2,  <1>1, <1>4, MaxBallotProp
  <2>2. maxBal[a] \in {-1} \cup Ballot
    BY DEF TypeOK
  <2>3. \A b \in {-1} \cup Ballot : -1 =< b
    BY SimpleArithmetic DEF Ballot
  <2>4. QED
    BY <2>1, <2>2, <2>3
<1>5. CASE S # {}
  <2>1. MaxBallot(S) \in S
    BY <1>2,  <1>5,  MaxBallotProp
  <2>2. QED
    BY <1>1, <1>3, <2>1
<1>6. QED
  BY <1>4, <1>5

LEMMA PmaxBalLemma5 ==
        TypeOK /\ bmsgsFinite =>
            \A a \in Acceptor : PmaxBal[a] \in Ballot \cup {-1}
<1> SUFFICES ASSUME TypeOK, bmsgsFinite, NEW a \in Acceptor
             PROVE  PmaxBal[a] \in Ballot \cup {-1}
  OBVIOUS
<1> DEFINE S == {m.bal : m \in {ma \in bmsgs : /\ ma.type \in {"1b", "2b"}
                                               /\ ma.acc = a}}
<1>1. /\ S \subseteq (Ballot \cup {-1})
      /\ IsFiniteSet(S)
  <2> DEFINE M == {ma \in bmsgs : /\ ma.type \in {"1b", "2b"}
                                  /\ ma.acc = a}
  <2>1. IsFiniteSet(M)
    BY SubsetOfFiniteSetFinite DEF bmsgsFinite, 1bOr2bMsgs
  <2>2. IsFiniteSet(S)
    <3> DEFINE f[x \in M] == x.bal
    <3>1. S = {f[x] : x \in M}
      OBVIOUS
    <3> HIDE DEF f, S, M
    <3>2 QED
      BY <2>1, <3>1, ImageOfFiniteSetFinite
  <2>3. \A m \in M : m.bal \in Ballot \cup {-1}
    <3> SUFFICES ASSUME NEW m \in M
                 PROVE  m.bal \in Ballot \cup {-1}
      OBVIOUS
    <3>1. m \in bmsgs /\ m.type \in {"1b", "2b"}
      OBVIOUS
    <3>2. CASE m.type = "1b"
      BY <3>1, <3>2, BMessageLemma DEF TypeOK, 1bMessage
    <3>3. CASE m.type = "2b"
      BY <3>1, <3>3, BMessageLemma DEF TypeOK, 2bMessage
    <3>4. QED
      BY <3>1, <3>2, <3>3
  <2> QED
    BY <2>2, <2>3
<1>2. QED
  BY <1>1, (* , <1>2, *) MaxBallotProp DEF PmaxBal, 1bOr2bMsgs

-----------------------------------------------------------------------------
(***************************************************************************)
(* Now comes a bunch of useful lemmas.                                     *)
(***************************************************************************)

(***************************************************************************)
(* We first prove that P!NextDef is a valid theorem and give it the name   *)
(* PNextDef.  This requires proving that the assumptions of module         *)
(* PConProof are satisfied by the refinement mapping.  Note that           *)
(* P!NextDef!: is an abbreviation for the statement of theorem P!NextDef   *)
(* -- that is, for the statement of theorem NextDef of module PConProof    *)
(* under the substitutions of the refinement mapping.                      *)
(***************************************************************************)
LEMMA PNextDef == P!NextDef!:
<1>1. P!QA
  BY QuorumTheorem
<1>2. P!BallotAssump
  BY BallotAssump DEF Ballot, P!Ballot, ByzAcceptor
<1>3. QED
  BY P!NextDef, <1>1, <1>2, NoSetContainsEverything

(***************************************************************************)
(* The provers have a hard time dealing with all the quantifiers inside    *)
(* the definition of KnowsSafeAt.  To help them, we define some formulas   *)
(* that allow us to break it into pieces.                                  *)
(***************************************************************************)
KSet(a, b) == {m \in knowsSent[a] : m.bal = b}
KS11a(a, S) == \E m \in S : /\ m.acc = a
                            /\ m.mbal = -1
KS11(BQ, S) == \A a \in BQ : KS11a(a, S)
KS1(S) == \E BQ \in ByzQuorum : KS11(BQ, S)
KS21BQa(v, c, a, S) == \E m \in S : /\ m.acc = a
                                    /\ m.mbal =< c
                                    /\ (m.mbal = c) => (m.mval = v)
KS21BQ(v, c, BQ, S) == \A a \in BQ : KS21BQa(v, c, a, S)
KS21(v,c,S) == \E BQ \in ByzQuorum : KS21BQ(v, c, BQ, S)
KS22WQa(v, c, a, S) == \E m \in S : /\ m.acc = a
                                    /\ \E r \in m.m2av : /\ r.bal >= c
                                                         /\ r.val = v
KS22WQ(v, c, WQ, S) == \A a \in WQ : KS22WQa(v, c, a,  S)
KS22(v, c,S) == \E WQ \in WeakQuorum : KS22WQ(v, c, WQ, S)
KS2(v,b,S) == \E c \in 0..(b-1) : /\ KS21(v, c, S)
                                  /\ KS22(v, c, S)

(***************************************************************************)
(* The following lemma asserts the obvious relation between KnowsSafeAt    *)
(* and the top-level definitions KS1, KS2, and KSet.  The second conjunct  *)
(* is, of course, the primed version of the first.  To understand why it   *)
(* is needed, see the discussion of MsgsTypeLemmaPrime below.              *)
(***************************************************************************)
LEMMA KnowsSafeAtDef ==
        \A a, b, v :
           /\ KnowsSafeAt(a, b, v) = (KS1(KSet(a,b)) \/ KS2(v, b, KSet(a, b)))
           /\ KnowsSafeAt(a, b, v)' = (KS1(KSet(a,b)') \/ KS2(v, b, KSet(a, b)'))
  BY DEF KnowsSafeAt, KSet, KS11a, KS11, KS1, KS21BQa,
          KS21BQ, KS21, KS22WQa, KS22WQ, KS22, KS2

LEMMA MsgsTypeLemma ==
        \A m \in msgs : /\ (m.type = "1a") <=> (m \in msgsOfType("1a"))
                        /\ (m.type = "1b") <=> (m \in 1bmsgs)
                        /\ (m.type = "1c") <=> (m \in 1cmsgs)
                        /\ (m.type = "2a") <=> (m \in 2amsgs)
                        /\ (m.type = "2b") <=> (m \in acceptorMsgsOfType("2b"))
<1> SUFFICES ASSUME NEW m \in msgs
             PROVE MsgsTypeLemma!(m)
  OBVIOUS
<1>1. (m \in msgsOfType("1a")) => (m.type = "1a")
  BY DEF msgsOfType
<1>2. (m \in 1bmsgs) => (m.type = "1b")
  <2> \A mm : [type |-> "1b", acc |-> mm.acc, bal |-> mm.bal,
                mbal |-> mm.mbal, mval |-> mm.mval].type = "1b"
    OBVIOUS
  <2> QED
    BY DEF 1bmsgs, 1bRestrict
<1>3. (m \in 1cmsgs) => (m.type = "1c")
  BY DEF 1cmsgs, msgsOfType
<1>4. (m \in 2amsgs) => (m.type = "2a")
  BY DEF 2amsgs
<1>5. (m \in acceptorMsgsOfType("2b")) => (m.type = "2b")
  BY DEF acceptorMsgsOfType, msgsOfType
<1>6. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF msgs

(***************************************************************************)
(* The following lemma is the primed version of MsgsTypeLemma.  That is,   *)
(* its statement is just the statement of MsgsTypeLemma primed.  It        *)
(* follows from MsgsTypeLemma by the meta-theorem that if we can prove a   *)
(* state-predicate F as a (top-level) theorem, then we can deduce F'.  A   *)
(* more general meta-theorem says that if we can prove a state predicate F *)
(* that does not appear within the proof of an ASSUME/PROVE, then we can   *)
(* deduce F'.  We expect this meta-theorem will be enshrined in a proof    *)
(* rule when temporal-logic reasoning is implemented in TLAPS.  Until      *)
(* then, we must prove F' separately from F.                               *)
(***************************************************************************)
LEMMA MsgsTypeLemmaPrime ==
        \A m \in msgs' : /\ (m.type = "1a") <=> (m \in msgsOfType("1a")')
                         /\ (m.type = "1b") <=> (m \in 1bmsgs')
                         /\ (m.type = "1c") <=> (m \in 1cmsgs')
                         /\ (m.type = "2a") <=> (m \in 2amsgs')
                         /\ (m.type = "2b") <=> (m \in acceptorMsgsOfType("2b")')
<1> SUFFICES ASSUME NEW m \in msgs'
             PROVE  MsgsTypeLemmaPrime!(m)
  OBVIOUS
<1>1. (m \in msgsOfType("1a")') => (m.type = "1a")
  BY DEF msgsOfType
<1>2. (m \in 1bmsgs') => (m.type = "1b")
  <2> \A mm : [type |-> "1b", acc |-> mm.acc, bal |-> mm.bal,
                mbal |-> mm.mbal, mval |-> mm.mval].type = "1b"
    OBVIOUS
  <2> QED
    BY DEF 1bmsgs, 1bRestrict
<1>3. (m \in 1cmsgs') => (m.type = "1c")
  BY DEF 1cmsgs, msgsOfType
<1>4. (m \in 2amsgs') => (m.type = "2a")
  BY DEF 2amsgs
<1>5. (m \in acceptorMsgsOfType("2b")') => (m.type = "2b")
  BY DEF acceptorMsgsOfType, msgsOfType
<1>6. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF msgs

(***************************************************************************)
(* The following lemma describes how msgs is changed by the actions of the *)
(* algorithm.                                                              *)
(***************************************************************************)
LEMMA MsgsLemma ==
TypeOK =>
    /\ \A self \in Acceptor, b \in Ballot :
         Phase1b(self, b) =>
            msgs' = msgs \cup
                     {[type |-> "1b", acc |-> self, bal |-> b,
                       mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
    /\ \A self \in Acceptor, b \in Ballot :
         Phase2av(self, b) =>
            \/ msgs' = msgs
            \/ \E v \in Value :
                 /\ [type |-> "1c", bal |-> b, val |-> v] \in msgs
                 /\ msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]}
    /\ \A self \in Acceptor, b \in Ballot :
          Phase2b(self, b) =>
             \E v \in Value :
               /\ \E Q \in ByzQuorum :
                    \A a \in Q :
                       \E m \in sentMsgs("2av", b) : /\ m.val = v
                                                     /\ m.acc = a
               /\ msgs' = msgs \cup
                            {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
               /\ bmsgs' = bmsgs \cup
                            {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
               /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
    /\ \A self \in Acceptor, b \in Ballot :
          LearnsSent(self, b) =>
            \E S \in SUBSET {m \in msgsOfType("1c") : m.bal = b} :
                     msgs' = msgs \cup S
    /\ \A self \in Ballot :
         Phase1a(self) =>
           msgs' = msgs \cup {[type |-> "1a", bal |-> self]}
    /\ \A self \in Ballot :
         Phase1c(self) =>
           \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
              /\ \A m \in S :
                    \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)
              /\ msgs' = msgs \cup S
    /\ \A self \in FakeAcceptor : FakingAcceptor(self) => msgs' = msgs
<1>a. ASSUME NEW S, bmsgs' = bmsgs \cup S
      PROVE  (\A m \in S : m.type # "1a") =>
                   (msgsOfType("1a")' = msgsOfType("1a"))
    BY <1>a DEF msgsOfType
<1>b. ASSUME NEW S, bmsgs' = bmsgs \cup S
      PROVE  (\A m \in S : m.type # "1b") => (1bmsgs' = 1bmsgs)
    BY <1>b DEF 1bmsgs, 1bRestrict, acceptorMsgsOfType, msgsOfType
<1>c. ASSUME NEW S, bmsgs' = bmsgs \cup S
      PROVE  (\A m \in S : m.type # "1c") /\ (knowsSent' = knowsSent)
                   => (1cmsgs' = 1cmsgs)
    <2>1. (knowsSent' = knowsSent) =>
             \A a \in Acceptor :
                \A b, v : KnowsSafeAt(a, b, v)' = KnowsSafeAt(a, b, v)
      BY  DEF KnowsSafeAt
    <2>2. (knowsSent' = knowsSent) =>
            \A b, v : (\E a \in Acceptor : KnowsSafeAt(a, b, v)') <=>
                          (\E a \in Acceptor : KnowsSafeAt(a, b, v))
      BY <2>1
    <2>3. (\A m \in S : m.type # "1c") => msgsOfType("1c")' = msgsOfType("1c")
      BY <1>c DEF msgsOfType
    <2>4. QED
      BY  <2>1, <2>2, <2>3 DEF 1cmsgs, KnowsSafeAt
<1>d. ASSUME NEW S, bmsgs' = bmsgs \cup S
      PROVE  (\A m \in S : m.type # "2av") => (2amsgs' = 2amsgs)
    <3> SUFFICES ASSUME \A m \in S : m.type # "2av"
                 PROVE  2amsgs' = 2amsgs
      OBVIOUS
    <3>1. acceptorMsgsOfType("2av")' = acceptorMsgsOfType("2av")
        BY <1>d DEF acceptorMsgsOfType, msgsOfType
    <3>2. QED
      BY <3>1 DEF 2amsgs
<1>e. ASSUME NEW S, bmsgs' = bmsgs \cup S
      PROVE  (\A m \in S : m.type # "2b") =>
                   (acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b"))
    BY <1>e DEF acceptorMsgsOfType, msgsOfType
<1> HAVE TypeOK
<1>1. ASSUME NEW self \in Acceptor, NEW b \in Ballot
      PROVE  Phase1b(self, b) =>
               msgs' = msgs \cup
                        {[type |-> "1b", acc |-> self, bal |-> b,
                          mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
  <2> DEFINE m == [type |-> "1b", acc |-> self, bal |-> b,
                   m2av |-> 2avSent[self],
                   mbal |-> maxVBal[self], mval |-> maxVVal[self]]
  <2> SUFFICES ASSUME Phase1b(self, b)
               PROVE  msgs' = msgs \cup {1bRestrict(m)}
    BY DEF 1bRestrict
  <2>1. bmsgs' = bmsgs \cup {m}
    <3>1. [type |-> "1b", bal |-> b, acc |-> self, m2av |-> 2avSent[self],
           mbal |-> maxVBal[self], mval |-> maxVVal[self]]
            = m
       \* The provers seem to be really bad at equality of records,
       \* so I had to jump through hoops to get it to prove this
       \* trivial result.
       <4> DEFINE a0 == "1b"
                  a1 == 2avSent[self]
                  a3 == maxVBal[self]
                  a4 == maxVVal[self]
                  a5 == b
                  a6 == self
       <4> HIDE DEF a0, a1, a3, a4, a5, a6
       <4>1. [type |-> a0, bal |-> a5, acc |-> a6,
                   m2av |-> a1, mbal |-> a3, mval |-> a4]
             =
             [type |-> a0, acc |-> a6, bal |-> a5,
                   m2av |-> a1, mbal |-> a3, mval |-> a4]
         BY SlowAuto \* OBVIOUS  \* It takes Isabelle 1-1/2 minutes to prove this.
       <4> USE DEF a0, a1, a3, a4, a5, a6
       <4>2. QED
         BY  <4>1
    <3> HIDE DEF m
    <3>2. QED
      BY <3>1 DEF Phase1b
  <2>2. /\ m.type = "1b"
         /\ m.acc = self
    OBVIOUS
  <2> HIDE DEF m
  <2>3. acceptorMsgsOfType("1b")' = acceptorMsgsOfType("1b") \cup {m}
    BY <2>1,  <2>2 DEF acceptorMsgsOfType, msgsOfType
  <2>4. 1bmsgs' = 1bmsgs \cup {1bRestrict(m)}
    BY <2>3 DEF 1bmsgs
  <2>5. knowsSent' = knowsSent
    BY DEF Phase1b
  <2>6. /\ msgsOfType("1a")' =  msgsOfType("1a")
        /\ 1cmsgs' = 1cmsgs
        /\ 2amsgs' = 2amsgs
        /\ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
    <3> DEFINE S == {m}
    <3> /\ bmsgs' = bmsgs \cup S
        /\ \A mm \in S : mm.type = "1b"
      BY <2>1, <2>2
    <3> HIDE DEF S
    <3> QED
       BY <2>5, <1>a, <1>c, <1>d, <1>e
  <2>7. QED
    BY <2>4, <2>6 DEF msgs

<1>2. ASSUME NEW self \in Acceptor, NEW b \in Ballot
      PROVE  Phase2av(self, b) =>
               \/ msgs' = msgs
               \/ \E v \in Value :
                    /\ [type |-> "1c", bal |-> b, val |-> v] \in msgs
                    /\ msgs' = msgs \cup
                                {[type |-> "2a", bal |-> b, val |-> v]}
  <2> HAVE Phase2av(self, b)
  <2>1. PICK m \in sentMsgs("1c", b) :
               /\ KnowsSafeAt(self, b, m.val)
               /\ bmsgs' = bmsgs \cup
                    {[type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]}
    BY DEF Phase2av
  <2>2. m = [type |-> "1c", bal |-> b, val |-> m.val]
    <3>1. /\ m \in bmsgs
          /\ m.type = "1c"
          /\ m.bal = b
      BY DEF sentMsgs
    <3>2. m \in BMessage
      BY <3>1 DEF TypeOK
    <3>3. m \in 1cMessage
      BY <3>1, <3>2, BMessageLemma
    <3>4. m = [type |-> m.type, bal |-> m.bal, val |-> m.val]
      BY <3>3 DEF 1cMessage
    <3>5. QED
      BY <3>1, <3>4

  <2> DEFINE ma == [type |-> "2a", bal |-> b, val |-> m.val]
  <2>3. SUFFICES ASSUME msgs' # msgs
                 PROVE  /\ m \in msgs
                        /\ msgs' = msgs \cup {ma}
    <3>1. m.val \in Value
      <4>1. /\ m \in bmsgs
            /\ m.type = "1c"
        BY DEF sentMsgs
      <4>2. m \in BMessage
        BY <4>1 DEF TypeOK
      <4>3. m \in 1cMessage
        BY <4>1, <4>2, BMessageLemma
      <4>4. QED
        BY <4>3 DEF 1cMessage
    <3>2. QED
      BY <3>1, <2>2

  <2>4. m \in msgs
    <3>1. /\ m \in bmsgs
          /\ m.type = "1c"
          /\ m.bal = b
      BY DEF sentMsgs
    <3>2. m \in msgsOfType("1c")
       BY <3>1 DEF msgsOfType
    <3>3. KnowsSafeAt(self, m.bal, m.val)
      BY <2>1, <3>1
    <3>4. \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)
      BY <3>3
    <3>5. m \in 1cmsgs
      BY <2>2, <3>1, <3>2, <3>4 DEF 1cmsgs
    <3>6. QED
      BY <3>5 DEF msgs
  <2>5. msgs' = msgs \cup {ma}
    <3> DEFINE mb == [type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]
               S == {mb}
    <3>1. /\ bmsgs' = bmsgs \cup S
          /\ \A mm \in S : mm.type = "2av"
      BY <2>1
    <3>2. knowsSent' = knowsSent
      BY DEF Phase2av
    <3>3. /\ msgsOfType("1a")' = msgsOfType("1a")
          /\ 1bmsgs' = 1bmsgs
          /\ 1cmsgs' = 1cmsgs
          /\ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
      <4> HIDE DEF S
      <4> QED
        BY <3>1, <3>2, <1>a, <1>b, <1>c, <1>e
    <3>4. 2amsgs \subseteq 2amsgs'
      <4>1. SUFFICES ASSUME NEW m1 \in [type : {"2a"}, bal : Ballot, val : Value],
                            \E Q \in Quorum :
                              \A a \in Q :
                               \E m2av \in acceptorMsgsOfType("2av") :
                                  /\ m2av.acc = a
                                  /\ m2av.bal = m1.bal
                                  /\ m2av.val = m1.val
                     PROVE  \E Q \in Quorum :
                              \A a \in Q :
                                \E m2av \in acceptorMsgsOfType("2av")' :
                                  /\ m2av.acc = a
                                  /\ m2av.bal = m1.bal
                                  /\ m2av.val = m1.val
        BY DEF 2amsgs
      <4>2. PICK Q \in Quorum :
                   \A a \in Q :
                      \E m2av \in acceptorMsgsOfType("2av") :
                         /\ m2av.acc = a
                         /\ m2av.bal = m1.bal
                         /\ m2av.val = m1.val
        BY <4>1
      <4> SUFFICES ASSUME NEW a \in Q
                   PROVE \E m2av \in acceptorMsgsOfType("2av")' :
                           /\ m2av.acc = a
                           /\ m2av.bal = m1.bal
                           /\ m2av.val = m1.val
        OBVIOUS
      <4>3. \E m2av \in acceptorMsgsOfType("2av") :
              /\ m2av.acc = a
              /\ m2av.bal = m1.bal
              /\ m2av.val = m1.val
        BY <4>2
      <4>4. acceptorMsgsOfType("2av") \subseteq acceptorMsgsOfType("2av")'
        <5>1. msgsOfType("2av") \subseteq msgsOfType("2av")'
          BY <3>1 DEF msgsOfType
        <5>2. QED
          BY <5>1 DEF acceptorMsgsOfType
      <4>5. QED
        BY <4>3, <4>4
    <3>5. msgs \subseteq msgs'
      BY <3>3, <3>4 DEF msgs
    <3>6. ASSUME NEW mp \in msgs', mp \notin msgs
          PROVE  mp = ma
      <4>1. mp \in 2amsgs' /\ mp \notin 2amsgs
        BY <3>3, <3>6 DEF msgs
      <4>2. PICK Q \in Quorum :
                  \A a \in Q :
                    \E m2av \in acceptorMsgsOfType("2av")' :
                      /\ m2av.acc = a
                      /\ m2av.bal = mp.bal
                      /\ m2av.val = mp.val
        BY <4>1 DEF 2amsgs
      <4>3. ~\A a \in Q :
                \E m2av \in acceptorMsgsOfType("2av") :
                   /\ m2av.acc = a
                   /\ m2av.bal = mp.bal
                   /\ m2av.val = mp.val
        BY <4>1 DEF 2amsgs
      <4>4. PICK a \in Q :
                  ~\E m2av \in acceptorMsgsOfType("2av") :
                     /\ m2av.acc = a
                     /\ m2av.bal = mp.bal
                     /\ m2av.val = mp.val
        BY <4>3
      <4>5. PICK m2av \in acceptorMsgsOfType("2av")' :
                    /\ m2av.acc = a
                    /\ m2av.bal = mp.bal
                    /\ m2av.val = mp.val
        BY <4>2
      <4>6. m2av \notin acceptorMsgsOfType("2av")
        BY <4>5, <4>4
      <4>7. m2av = mb
        <5>1. acceptorMsgsOfType("2av")' = acceptorMsgsOfType("2av") \cup {mb}
          BY <3>1, mb.type = "2av" DEF acceptorMsgsOfType, msgsOfType
        <5>2. QED
          BY <4>6, <5>1
      <4>8. mp = [type |-> "2a", bal |-> mp.bal, val |-> mp.val]
        <5>1. mp \in [type : {"2a"}, bal : Ballot, val : Value]
          BY <4>1 DEF 2amsgs
        <5>2. QED
          BY <5>1
      <4>9. QED
        BY <4>8, <4>7, <4>5
    <3>7. QED
      BY <2>3, <3>5, <3>6
  <2>6. QED
    BY <2>4, <2>5

<1>3. ASSUME NEW self \in Acceptor, NEW b \in Ballot
      PROVE  Phase2b(self, b) =>
                \E v \in Value :
                  /\ \E Q \in ByzQuorum :
                       \A a \in Q :
                          \E m \in sentMsgs("2av", b) : /\ m.val = v
                                                        /\ m.acc = a
                  /\ msgs' = msgs \cup
                               {[type |-> "2b", acc |-> self, bal |-> b,
                                  val |-> v]
                                 }
                  /\ bmsgs' = bmsgs \cup
                            {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
                  /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
  <2> HAVE Phase2b(self, b)
  <2>1. PICK v \in Value :
               /\ \E Q \in ByzQuorum :
                    \A a \in Q :
                       \E m \in sentMsgs("2av", b) : /\ m.val = v
                                                     /\ m.acc = a
               /\ bmsgs' =
                    bmsgs \cup
                     {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
               /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
    BY DEF Phase2b
  <2> DEFINE bm == [type |-> "2b", acc |-> self, bal |-> b, val |-> v]
  <2>2. /\ msgsOfType("1a")' = msgsOfType("1a")
        /\ 1bmsgs' = 1bmsgs
        /\ 1cmsgs' = 1cmsgs
        /\ 2amsgs' = 2amsgs
    <3> DEFINE S == {bm}
    <3> /\ bmsgs' = bmsgs \cup S
        /\ \A m \in S : m.type = "2b"
      BY <2>1, bm.type = "2b"
    <3> HIDE DEF S
    <3> QED
      BY <1>a, <1>b, knowsSent' = knowsSent,  <1>c, <1>d DEF Phase2b
  <2>3. acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b") \cup {bm}
    <3>0. acceptorMsgsOfType("2b") \subseteq acceptorMsgsOfType("2b")'
      BY <2>1 DEF acceptorMsgsOfType, msgsOfType
    <3>1. bm \in acceptorMsgsOfType("2b")'
      BY <2>1  DEF acceptorMsgsOfType, msgsOfType
    <3>3. ASSUME NEW m \in acceptorMsgsOfType("2b")', m # bm
          PROVE  m \in acceptorMsgsOfType("2b")
      <4>1. /\ m \in bmsgs'
            /\ m.type = "2b"
            /\ m.acc \in Acceptor
        BY DEF acceptorMsgsOfType, msgsOfType
      <4>a. bmsgs' = bmsgs \cup {bm}
        BY <2>1
      <4>2. m \in bmsgs
        BY  <4>1, <2>1, (* bmsgs' = bmsgs \cup {bm},*)  <3>3
      <4>3. QED
        BY <4>1, <4>2 DEF acceptorMsgsOfType, msgsOfType
    <3>5. QED
      BY <3>0, <3>1, <3>3

  <2>4. msgs' = msgs \cup {bm}
    BY <2>2, <2>3 DEF msgs
  <2>5. QED
    BY <2>1, <2>4 \*, <2>5

<1>4. ASSUME NEW self \in Acceptor, NEW b \in Ballot
      PROVE  LearnsSent(self, b) =>
               \E S \in SUBSET {m \in msgsOfType("1c") : m.bal = b} :
                           msgs' = msgs \cup S
  <2> HAVE LearnsSent(self, b)
  <2>1. /\ msgsOfType("1a")' = msgsOfType("1a")
        /\ 1bmsgs' = 1bmsgs
        /\ 2amsgs' = 2amsgs
        /\ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
    <3>1. /\ bmsgs' = bmsgs \cup {}
          /\ \A m \in {} : m.type = "x"
      BY DEF LearnsSent
    <3>2. <2>1!1
      BY <3>1, <1>a
    <3>3. <2>1!2
      BY <3>1, <1>b
    <3>4. <2>1!3
      BY <3>1, <1>d
    <3>5. <2>1!4
      BY <3>1, <1>e
    <3>6. QED
      BY <3>2, <3>3, <3>4, <3>5
  <2>2. /\ 1cmsgs \subseteq 1cmsgs'
        /\ \A m \in 1cmsgs' \ 1cmsgs :
               m \in msgsOfType("1c") /\ m.bal = b
    <3>1. bmsgs' = bmsgs
      BY DEF LearnsSent
    <3>2. PICK S \in SUBSET sentMsgs("1b", b):
             knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
      BY DEF LearnsSent
    <3>3. ASSUME NEW m \in 1cmsgs
          PROVE  m \in 1cmsgs'
      <4>1. \A a \in Acceptor : knowsSent[a] \subseteq knowsSent'[a]
        BY <3>2 DEF TypeOK
      <4>2. \A a \in Acceptor :
               \A bb, v : KnowsSafeAt(a, bb, v) => KnowsSafeAt(a, bb, v)'
        <5> SUFFICES ASSUME NEW a \in Acceptor, NEW bb, NEW v,
                            KnowsSafeAt(a, bb, v)
                     PROVE  KnowsSafeAt(a, bb, v)'
          OBVIOUS
        <5>1. \A T, U : (T \subseteq U) => /\ KS1(T) => KS1(U)
                                           /\ KS2(v, bb, T) => KS2(v, bb, U)
          <6> SUFFICES ASSUME NEW T, NEW U, T \subseteq U
                       PROVE  <5>1!(T, U)!2
            OBVIOUS
          <6>1. <5>1!(T, U)!2!1
            <7> SUFFICES ASSUME NEW BQ
                         PROVE  KS11(BQ, T) => KS11(BQ, U)
              BY DEF KS1
            <7> SUFFICES ASSUME NEW ac
                         PROVE  KS11a(ac, T) => KS11a(ac, U)
              BY DEF KS11
            <7> QED
              BY DEF   KS11a
          <6>2. <5>1!(T, U)!2!2
            <7>1 ASSUME NEW c
                        PROVE KS21(v, c, T) => KS21(v, c, U)
              <8> SUFFICES ASSUME NEW BQ
                           PROVE  KS21BQ(v, c, BQ, T) => KS21BQ(v, c, BQ, U)
                BY DEF KS21
              <8> SUFFICES ASSUME NEW ac
                           PROVE  KS21BQa(v, c, ac, T) => KS21BQa(v, c, ac, U)
                BY DEF KS21BQ
              <8> QED
                BY DEF KS21BQa
            <7>2 ASSUME NEW c
                        PROVE KS22(v, c, T) => KS22(v, c, U)
              <8> SUFFICES ASSUME NEW WQ
                           PROVE  KS22WQ(v, c, WQ, T) => KS22WQ(v, c, WQ, U)
                BY DEF KS22
              <8> SUFFICES ASSUME NEW ac
                           PROVE  KS22WQa(v, c, ac, T) => KS22WQa(v, c, ac, U)
                BY DEF KS22WQ
              <8> QED
                BY DEF KS22WQa
            <7>3. QED
              BY <7>1, <7>2 DEF KS2
          <6>3. QED
            BY <6>1, <6>2
        <5>2. KSet(a, bb) \subseteq  KSet(a, bb)'
          BY <4>1 DEF KSet
        <5>3. QED
          BY  <5>1, <5>2, KnowsSafeAtDef
      <4>3. msgsOfType("1c")' = msgsOfType("1c")
        BY DEF msgsOfType, LearnsSent
      <4>4. QED
        BY <4>2, <4>3 DEF 1cmsgs
    <3>4. ASSUME NEW m \in 1cmsgs', m \notin 1cmsgs
          PROVE  m \in msgsOfType("1c") /\ m.bal = b
      <4>1. m \in msgsOfType("1c")
        BY DEF 1cmsgs, msgsOfType, LearnsSent
      <4>2. PICK a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)'
        BY DEF 1cmsgs
      <4>3. ~KnowsSafeAt(a, m.bal, m.val)
        BY <3>4, <4>1 DEF 1cmsgs
      <4>4. \A aa \in Acceptor, bb \in Ballot :
               \A mm \in KSet(aa, bb)' :
                   mm \notin KSet(aa, bb) => bb = b
        <5>1. SUFFICES ASSUME NEW aa \in Acceptor,
                              NEW bb \in Ballot,
                              NEW mm \in KSet(aa, bb)',
                              mm \notin  KSet(aa, bb)
                       PROVE  bb = b
          OBVIOUS
        <5>2. ASSUME NEW m1 \in knowsSent[aa]', m1 \notin knowsSent[aa]
              PROVE  m1.bal = b
          <6>1. knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \union S]
            BY <3>2
          <6>2. CASE aa # self
            BY <6>2, <5>2 DEF TypeOK, LearnsSent
          <6>3. CASE aa = self
             BY <6>1, <6>3, <5>2 DEF TypeOK, sentMsgs
          <6>4. QED
            BY <6>2, <6>3
        <5>3. QED
          BY <5>1, <5>2 DEF KSet
      <4>5. m.bal \in Ballot
        BY <4>1, BMessageLemma DEF 1cMessage, msgsOfType, TypeOK
      <4>7. CASE KS1(KSet(a,m.bal)') /\ ~KS1(KSet(a,m.bal))
        <5>1. PICK BQ \in ByzQuorum : KS11(BQ, KSet(a, m.bal)')
          BY <4>7 DEF KS1
        <5>2. ~ KS11(BQ, KSet(a, m.bal))
          BY <4>7 DEF KS1
        <5>3. PICK aa \in BQ : ~KS11a(aa, KSet(a, m.bal))
          BY <5>2 DEF KS11
        <5>4. KS11a(aa, KSet(a, m.bal)')
          BY <5>1 DEF KS11
        <5>5. PICK mm \in KSet(a, m.bal)' : mm.acc = aa /\ mm.mbal = -1
          BY <5>4 DEF KS11a
        <5>6. mm \notin KSet(a, m.bal)
          BY <5>5, <5>3 DEF KS11a
        <5>7. m.bal = b
          BY <4>4, <4>5, <5>5, <5>6
        <5>8. QED
          BY <4>1, <5>7
      <4>8. CASE KS2(m.val, m.bal, KSet(a, m.bal)') /\ ~KS2(m.val, m.bal, KSet(a, m.bal))
        <5>1. PICK c \in 0..(m.bal-1) : /\ KS21(m.val, c, KSet(a, m.bal))'
                                        /\ KS22(m.val, c, KSet(a, m.bal))'
          BY <4>8 DEF KS2
        <5>2. CASE ~KS21(m.val, c, KSet(a, m.bal))
          <6>1. PICK BQ \in ByzQuorum : KS21BQ(m.val, c, BQ, KSet(a, m.bal))'
            BY <5>1 DEF KS21
          <6>2. PICK aa \in BQ :
                      ~ \E mm \in KSet(a, m.bal) : /\ mm.acc = aa
                                                   /\ mm.mbal =< c
                                                   /\ (mm.mbal = c) => (mm.mval = m.val)
            BY <5>2 DEF KS21, KS21BQ, KS21BQa
          <6>3. PICK mm \in KSet(a, m.bal)' : /\ mm.acc = aa
                                              /\ mm.mbal =< c
                                              /\ (mm.mbal = c) => (mm.mval = m.val)
            BY <6>1 DEF KS21BQ, KS21BQa
          <6>4. mm \notin KSet(a, m.bal)
            BY <6>2, <6>3
          <6>5. mm.bal = m.bal
            BY DEF KSet
          <6>6. QED
            BY <6>4, <6>5, <4>4, <4>5, <4>1
        <5>3. CASE ~KS22(m.val, c, KSet(a, m.bal))
          <6>1. PICK WQ \in WeakQuorum : KS22WQ(m.val, c, WQ, KSet(a, m.bal))'
            BY <5>1 DEF KS22
          <6>2. PICK aa \in WQ :
                      ~ \E mm \in KSet(a, m.bal) : /\ mm.acc = aa
                                                   /\ \E r \in mm.m2av :
                                                         /\ r.bal >= c
                                                         /\ r.val = m.val
            <7>1. \neg ( \A aa \in WQ :
                   \E m_1 \in KSet(a, m.bal) :
                      /\ m_1.acc = aa
                      /\ \E r \in m_1.m2av : /\ r.bal \geq c
                                             /\ r.val = m.val)
               BY <5>3 DEF KS22, KS22WQ, KS22WQa
            <7>2. QED
              BY <7>1
          <6>3. PICK mm \in KSet(a, m.bal)' : /\ mm.acc = aa
                                              /\ \E r \in mm.m2av :
                                                         /\ r.bal >= c
                                                         /\ r.val = m.val
            BY <6>1 DEF KS22WQ, KS22WQa
          <6>4. mm \notin KSet(a, m.bal)
            BY <6>2, <6>3
          <6>5. mm.bal = m.bal
            BY DEF KSet
          <6>6. QED
            BY <6>4, <6>5, <4>4, <4>5, <4>1
        <5>4. QED
          BY <5>2, <5>3, <4>8 DEF KS2
      <4> QED
        <5>1. KS1(KSet(a,m.bal)') \/ KS2(m.val, m.bal, KSet(a, m.bal)')
          <6> KnowsSafeAt(a, m.bal, m.val)' = (KS1(KSet(a,m.bal)') \/ KS2(m.val, m.bal, KSet(a, m.bal)'))
             BY KnowsSafeAtDef
          <6> QED
            BY <4>2
        <5>2. (~KS1(KSet(a,m.bal))) /\ (~KS2(m.val, m.bal, KSet(a, m.bal)))
          BY <4>3, KnowsSafeAtDef
        <5>3. QED
          BY <4>7, <4>8, <5>1, <5>2
    <3>5. QED
      BY <3>3, <3>4
  <2>3. QED
    <3> DEFINE S == 1cmsgs' \ 1cmsgs
    <3>1. 1cmsgs' = 1cmsgs \cup S
      BY <2>2
    <3>2. S \in SUBSET {m \in msgsOfType("1c") : m.bal = b}
        BY <2>2
    <3> HIDE DEF S
    <3>3. msgs' = msgs \cup S
      BY <3>1, <2>1 DEF msgs
    <3>4. QED
      BY <3>3, <3>2
<1>5. ASSUME NEW self \in Ballot
      PROVE  Phase1a(self) =>
                msgs' = msgs \cup {[type |-> "1a", bal |-> self]}
  <2> DEFINE m == [type |-> "1a", bal |-> self]
  <2> SUFFICES ASSUME Phase1a(self)
               PROVE  msgs' = msgs \cup {m}
    BY <1>5
  <2>1. /\ bmsgs' = bmsgs \cup {m}
        /\ m.type = "1a"
    BY DEF Phase1a
  <2>2. /\ 1bmsgs' = 1bmsgs
        /\ 1cmsgs' = 1cmsgs
        /\ 2amsgs' = 2amsgs
        /\ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
    <3> DEFINE S == {m}
    <3> /\ bmsgs' = bmsgs \cup S
        /\ \A mm \in S : mm.type = "1a"
        /\ knowsSent' = knowsSent
      BY <2>1 DEF Phase1a
    <3> HIDE DEF S
    <3> QED
      BY <1>b, <1>c, <1>d, <1>e
  <2>3. msgsOfType("1a")' = msgsOfType("1a") \cup {m}
    BY <2>1 DEF msgsOfType
  <2>4. QED
    BY <2>2, <2>3 DEF msgs
<1>6. ASSUME NEW  self \in Ballot
      PROVE  Phase1c(self) =>
               \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
                 /\ \A m \in S :
                      \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)
                 /\ msgs' = msgs \cup S
  <2>1. SUFFICES ASSUME NEW S \in SUBSET [type : {"1c"}, bal : {self}, val : Value],
                        bmsgs' = (bmsgs \cup S),
                        knowsSent' = knowsSent
                 PROVE <1>6!2!2
    BY DEF Phase1c
  <2> DEFINE SS == {m \in S : \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)}
  <2> SUFFICES msgs' = msgs \cup SS
    BY <2>1
  <2>2. \A m \in S : m.type = "1c"
    BY <2>1
  <2>3. /\ msgsOfType("1a")' = msgsOfType("1a")
        /\ 1bmsgs' = 1bmsgs
        /\ 2amsgs' = 2amsgs
        /\ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
   BY <2>1, <2>2, <1>a, <1>b, <1>d, <1>e
  <2>4. 1cmsgs' = 1cmsgs \cup SS
    <3>1. msgsOfType("1c")' = msgsOfType("1c") \cup S
      BY <2>1 DEF msgsOfType
    <3>2. 1cmsgs' =
              {m \in msgsOfType("1c") :
                        \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)'}
                \cup
              {m \in S : \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)'}
      BY <3>1 DEF 1cmsgs
    <3>3. \A m : \A a \in Acceptor:
              KnowsSafeAt(a, m.bal, m.val)' = KnowsSafeAt(a, m.bal, m.val)
      BY <2>1 DEF KnowsSafeAt
    <3>4. 1cmsgs' =
              {m \in msgsOfType("1c") :
                        \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)}
                \cup
              {m \in S : \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)}
     BY <2>1, <3>2, <3>3
    <3>5. QED
      BY <3>4 DEF 1cmsgs
  <2>5. QED
    BY <2>3, <2>4 DEF msgs

<1>7. ASSUME NEW  self \in FakeAcceptor
      PROVE FakingAcceptor(self) => msgs' = msgs
  <2> SUFFICES ASSUME FakingAcceptor(self)
               PROVE  msgs' = msgs
    OBVIOUS
  <2>1. PICK m \in 1bMessage \cup 2avMessage \cup 2bMessage :
               /\ m.acc = self
               /\ bmsgs' = bmsgs \cup {m}
    BY DEF FakingAcceptor
  <2>2. m.type \in {"1b", "2av", "2b"}
    BY DEF 1bMessage, 2avMessage, 2bMessage
  <2>3. /\ msgsOfType("1a")' = msgsOfType("1a")
        /\ 1cmsgs' = 1cmsgs
    <3> S == {m}
    <3>1. bmsgs' = bmsgs \cup S
      BY <2>1
    <3>2. /\ \A mm \in S : mm.type # "1a"
          /\ \A mm \in S : mm.type # "1c"
      BY <2>1, <2>2
    <3> HIDE DEF S
    <3>3. knowsSent' = knowsSent
      BY DEF FakingAcceptor
    <3>4. QED
      BY <3>1, <3>2, <3>3, <1>a, <1>c
  <2>4. m.acc \notin Acceptor
    BY <2>1, BQA
  <2>5. 1bmsgs' = 1bmsgs
    <3>1. acceptorMsgsOfType("1b")' = acceptorMsgsOfType("1b")
      BY <2>1, <2>4  DEF acceptorMsgsOfType, msgsOfType
    <3>2. QED
      BY <3>1 DEF 1bmsgs
  <2>6. 2amsgs' = 2amsgs
    <3>1. acceptorMsgsOfType("2av")' = acceptorMsgsOfType("2av")
      BY <2>1, <2>4  DEF acceptorMsgsOfType, msgsOfType
    <3>2. QED
      BY <3>1 DEF 2amsgs
  <2>7. acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
    BY <2>1, <2>4  DEF acceptorMsgsOfType, msgsOfType
  <2>8. QED
    BY <2>3, <2>5, <2>6, <2>7 DEF msgs
<1>9. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7
-----------------------------------------------------------------------------
(***************************************************************************)
(* Finally, we come to the proof of invariance of our inductive invariant  *)
(* Inv.  Because TLAPS does not yet do temporal reasoning, we omit the     *)
(* proofs of the obviously true temporal-logic steps.                      *)
(***************************************************************************)
THEOREM Spec => []Inv
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init
               PROVE  Inv
    OBVIOUS
  <2> USE DEF Init
  <2>1. TypeOK
    BY  DEF TypeOK
  <2>2. bmsgsFinite
    BY EmptySetFinite DEF bmsgsFinite, 1bOr2bMsgs
  <2>3. 1bInv1
    BY DEF 1bInv1
  <2>4. 1bInv2
    BY DEF 1bInv2
  <2>5. maxBalInv
    BY DEF maxBalInv
  <2>6. 2avInv1
    BY DEF 2avInv1
  <2>7. 2avInv2
    BY DEF 2avInv2
  <2>8. 2avInv3
    BY DEF 2avInv3
  <2>9. accInv
    BY DEF accInv
  <2>10. knowsSentInv
    BY DEF knowsSentInv
  <2>11. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10
    DEF Inv

<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
               PROVE Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in Acceptor,
               NEW b \in Ballot,
               \/ Phase1b(self, b)
               \/ Phase2av(self, b)
               \/ Phase2b(self,b)
               \/ LearnsSent(self, b)
        PROVE  Inv'
    <3>1. CASE Phase1b(self, b)
      <4> USE Phase1b(self, b)
      <4> DEFINE mb == [type  |-> "1b", bal |-> b, acc |-> self,
                        m2av |-> 2avSent[self],
                        mbal |-> maxVBal[self], mval |-> maxVVal[self]]
                 mc == [type |-> "1b", acc |-> self, bal |-> b,
                        mbal |-> maxVBal[self], mval |-> maxVVal[self]]
      <4>1. msgs' = msgs \cup {mc}
        BY MsgsLemma DEF Inv
      <4>2. TypeOK'
        <5>1. mb \in BMessage
          BY  DEF Inv, TypeOK, BMessage, 1bMessage, ByzAcceptor
        <5>2. QED
          BY <5>1 DEF TypeOK, Inv, Phase1b
      <4>3. bmsgsFinite'
        BY FiniteMsgsLemma DEF Inv, bmsgsFinite, Phase1b
      <4>4. 1bInv1'
        <5>1. SUFFICES ASSUME NEW m \in bmsgs',
                              NEW r \in m.m2av,
                              1bInv1!(m)!1
                       PROVE  [type |-> "1c",
                               bal |-> r.bal, val |-> r.val] \in msgs'
          BY DEF 1bInv1
        <5>2. CASE m = mb
          BY <4>1, <5>1, <5>2 DEF Inv,  accInv
        <5>3. CASE m \in bmsgs
          BY <5>1, <5>3, <4>1 DEF Inv, 1bInv1
        <5>4. QED
          BY <5>2, <5>3 DEF Phase1b
      <4>5. 1bInv2'
        <5>1. ASSUME NEW m1 \in bmsgs, NEW m2 \in bmsgs,
                             1bInv2!(m1, m2)!1
              PROVE  m1 = m2
          BY <5>1 DEF Inv, 1bInv2
        <5>2. ASSUME NEW m1 \in bmsgs',
                     1bInv2!(m1, mb)!1
              PROVE m1 = mb
          <6>1. SUFFICES ASSUME m1 # mb
                         PROVE  FALSE
            OBVIOUS
          <6>2. m1 \in bmsgs
            BY <6>1 DEF Phase1b
          <6>3. m1.bal =< maxBal[self]
              BY <5>2, <6>2 DEF Inv, maxBalInv
          <6>4. b > maxBal[self]
            BY DEF Phase1b
          <6>5. m1.bal \in Ballot \cup {-1}
            BY <5>2, <6>2 DEF Inv, TypeOK, 1bMessage
          <6>6. maxBal[self] \in Ballot \cup {-1}
              BY DEF Inv, TypeOK
          <6>7. \A m1bal, maxbalself \in Ballot \cup {-1} :
                    b > maxbalself /\ m1bal =< maxbalself => m1bal # b
              BY SimpleArithmetic DEF Ballot
          <6>8. m1.bal # b
              BY <6>3, <6>4, <6>5, <6>6, <6>7
          <6>9. QED
              BY <5>2, <6>1, <6>8
        <5>3. QED
          <6> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                             1bInv2!(m1, m2)!1
                       PROVE  m1 = m2
             BY DEF 1bInv2
          <6>1. CASE m1 # mb /\ m2 # mb
             BY <6>1, <5>1 DEF Phase1b
          <6>2. CASE m1 = mb
            BY <5>2, <6>2
          <6>3. CASE m2 = mb
            BY <5>2, <6>3
          <6>4. QED
            BY <6>1, <6>2, <6>3
      <4>6. maxBalInv'
        <5>1. SUFFICES ASSUME NEW m \in bmsgs',
                              m.type \in {"1b", "2av", "2b"},
                              m.acc \in Acceptor
                       PROVE  m.bal =< maxBal'[m.acc]
          BY DEF maxBalInv
        <5>2. /\ \A x \in Ballot \cup {-1} :
                   (b > x)  => (x =< b)
              /\ \A x, y, z \in Ballot \cup {-1} :
                   (x =< y) /\ (y =< z) => (x =< z)
              /\ \A x \in Ballot \cup {-1} : x =< x
          BY SimpleArithmetic DEF Ballot
        <5>3. ASSUME NEW a \in Acceptor
              PROVE  /\ maxBal[a] =< maxBal'[a]
                     /\ maxBal[a] \in Ballot \cup {-1}
                     /\ maxBal'[a] \in Ballot \cup {-1}
          <6>1. <5>3!2!2 /\ <5>3!2!3
            BY <4>2 DEF Inv, TypeOK
          <6>2. maxBal[a] =< maxBal'[a]
            <7>1. CASE a = self
              BY <5>2, <6>1, <7>1 DEF Phase1b, Inv, TypeOK
            <7>2. CASE a # self
              BY <5>2, <7>2, <5>3 DEF Phase1b, Inv, TypeOK
            <7>3. QED
              BY <7>1, <7>2
          <6>3. QED
            BY <6>1, <6>2
        <5>4. CASE m \in bmsgs
          <6>1. m.bal =< maxBal[m.acc]
            BY <5>1, <5>4 DEF Inv, maxBalInv
          <6>2. m.bal \in  Ballot \cup {-1}
            <7>1. CASE m.type = "1b"
              BY <5>4, <7>1, BMessageLemma DEF Inv, TypeOK, 1bMessage
            <7>2. CASE m.type = "2av"
              BY <5>4, <7>2, BMessageLemma DEF Inv, TypeOK, 2avMessage
            <7>3. CASE m.type = "2b"
              BY <5>4, <7>3, BMessageLemma DEF Inv, TypeOK, 2bMessage
            <7>4. QED
              BY <7>1, <7>2, <7>3, <5>1
          <6>3. QED
            <7>1. /\ maxBal[m.acc] =< maxBal'[m.acc]
                  /\ maxBal[m.acc] \in Ballot \cup {-1}
                  /\ maxBal'[m.acc] \in Ballot \cup {-1}
              BY <5>1, <5>3
            <7>2. QED
             BY <6>1, <6>2, <7>1, <5>2
        <5>5. CASE m = mb
          BY <5>2, <5>5 DEF Inv, TypeOK, Phase1b
        <5>6. QED
          BY <5>4, <5>5 DEF Phase1b
      <4>7. 2avInv1'
        <5>1. SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                              2avInv1!(m1, m2)!1
                       PROVE  2avInv1!(m1, m2)!2'
          BY DEF 2avInv1
        <5>2. m1 # mb /\ m2 # mb
          BY <5>1 , mb.type = "1b"
        <5>3. m1 \in bmsgs /\ m2 \in bmsgs
          BY <5>2 DEF Phase1b
        <5>4. QED
          BY <5>1, <5>3 DEF Inv, 2avInv1
      <4>8. 2avInv2'
         <5>1. SUFFICES ASSUME NEW m \in bmsgs',
                               2avInv2!(m)!1
                        PROVE  \E r \in 2avSent'[m.acc] :
                                   /\ r.val = m.val
                                   /\ r.bal >= m.bal
          BY DEF 2avInv2
        <5>2. m # mb
          BY <5>1 , mb.type = "1b"
        <5>3. m \in bmsgs
          BY <5>2 DEF Phase1b
        <5>4. QED
          BY <5>1, <5>3 DEF Phase1b, Inv, 2avInv2
      <4>9. 2avInv3'
         <5>1. SUFFICES ASSUME NEW m \in bmsgs',
                               2avInv3!(m)!1
                        PROVE  2avInv3!(m)!2'
          BY DEF 2avInv3
        <5>2. m # mb
          BY <5>1 , mb.type = "1b"
        <5>3. m \in bmsgs
          BY <5>2 DEF Phase1b
        <5>4. QED
          BY <5>1, <5>3, <4>1 DEF Phase1b, Inv, 2avInv3
      <4>10. accInv'
        <5> SUFFICES ASSUME NEW a \in Acceptor,
                            NEW r \in 2avSent[a]
                     PROVE  /\ r.bal =< maxBal'[a]
                            /\ [type |-> "1c", bal |-> r.bal, val |-> r.val]
                                   \in msgs'
          BY DEF accInv, Phase1b
        <5>1. /\ r.bal =< maxBal[a]
              /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
          BY DEF Inv, accInv
        <5>2. [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
          BY <5>1, MsgsLemma DEF Inv
        <5>3. maxBal[a] =< maxBal'[a]
          <6>1. CASE a = self
            <7>1. \A maxbal \in Ballot \cup {-1} :
                     b > maxbal => maxbal =< b
              BY SimpleArithmetic DEF Ballot
            <7>2. QED
              BY <6>1, <7>1 DEF Phase1b, Inv, TypeOK
          <6>2. CASE a # self
            <7>1. \A maxbal \in Ballot \cup {-1} : maxbal =< maxbal
              BY SimpleArithmetic DEF Ballot
            <7>2. QED
              BY <6>2, <7>1 DEF Phase1b, Inv, TypeOK
          <6>3. QED
            BY <6>1, <6>2
        <5>4. r.bal =< maxBal'[a]
          <6>1. \A rbal, maxb, maxbp \in Ballot \cup {-1} :
                   rbal =< maxb /\ maxb =< maxbp =>  rbal =< maxbp
            BY SimpleArithmetic DEF Ballot
          <6>2. r.bal \in Ballot
            <7>1. 2avSent[a] \in SUBSET [val : Value, bal : Ballot]
              BY DEF Inv, TypeOK
            <7>2. r \in [val : Value, bal : Ballot]
              BY <7>1
            <7>3. QED
              BY <7>2
          <6>3. /\ maxBal[a] \in Ballot \cup {-1}
                /\ maxBal'[a] \in Ballot \cup {-1}
            BY <4>2 DEF Inv, TypeOK
          <6>4. QED
            BY <6>1, <6>2, <6>3, <5>1, <5>3
        <5>5. QED
          BY <5>2, <5>4
      <4>11. knowsSentInv'
        <5>1. msgsOfType("1b") \subseteq msgsOfType("1b")'
          BY DEF Phase1b, msgsOfType
        <5>2. QED
          BY <5>1 DEF Inv, knowsSentInv, Phase1b
      <4>12. QED
        BY <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9,
           <4>10, <4>11 DEF Inv
    <3>2. CASE Phase2av(self, b)
      <4> USE Phase2av(self, b)
      <4>1. PICK mc \in sentMsgs("1c", b) :
                   /\ KnowsSafeAt(self, b, mc.val)
                   /\ bmsgs' = bmsgs \cup
                                 {[type |-> "2av", bal |-> b,
                                   val |-> mc.val, acc |-> self]}
                   /\ 2avSent' = [2avSent EXCEPT
                        ![self] = {r \in 2avSent[self] : r.val # mc.val}
                                    \cup {[val |-> mc.val, bal |-> b]}]
        BY DEF Phase2av
      <4>2. mc = [type |-> "1c", bal |-> mc.bal, val |-> mc.val]
        \* Follows from <4>1 and def of sentMsgs (domain of mc).
        \* but provers are unable to prove this easily.
        <5>1. /\ mc \in [type : {"1c"}, bal : Ballot, val : Value]
              /\ mc.type = "1c"
          BY <4>1, BMessageLemma DEF sentMsgs, Inv, TypeOK, 1cMessage
        <5> DEFINE mcx == [type |-> "1c", bal |-> mc.bal, val |-> mc.val]
        <5>2. /\ mc = [i \in {"type", "bal", "val"} |-> mc[i]]
              /\ mcx = [i \in {"type", "bal", "val"} |-> mcx[i]]
          BY <5>1
        <5>3. \A i \in {"type", "bal", "val"} : mc[i] = mcx[i]
          <6> SUFFICES ASSUME NEW i \in {"type", "bal", "val"}
                       PROVE  mc[i] = mcx[i]
            OBVIOUS
          <6>1. CASE i = "type"
            BY <5>1, <6>1
          <6>2. CASE i = "bal"
             BY <6>2
          <6>3. CASE i = "val"
            BY <6>3
          <6>4. QED
            BY <6>1, <6>2, <6>3
        <5>4. QED
          BY  <5>2, <5>3
      <4> DEFINE mb == [type |-> "2av", bal |-> b,
                        val |-> mc.val, acc |-> self]
                 mmc(v) == [type |-> "1c", bal |-> b, val |-> v]
                 ma(v) == [type |-> "2a", bal |-> b, val |-> v]
      <4>3. \/ msgs' = msgs
            \/ \E v \in Value :
                 /\ mmc(v) \in msgs
                 /\ msgs' = msgs \cup {ma(v)}
        <5>1. MsgsLemma!2!2
          BY MsgsLemma DEF Inv
        <5>2. QED
          BY <5>1
      <4>4. msgs \subseteq msgs'
        BY <4>3
      <4>5. TypeOK'
        <5>1. mc \in 1cMessage
            BY mc.type = "1c", BMessageLemma DEF sentMsgs, Inv, TypeOK

        <5>2. mb.val \in Value
          <6>2. QED
            BY <5>1 DEF 1cMessage
        <5>3. TypeOK!1'
          BY DEF Inv, TypeOK, Phase2av
        <5>4. TypeOK!2'
          <6>1. 2avSent[self] \in SUBSET [val : Value, bal : Ballot]
            BY DEF Inv, TypeOK
          <6>2. {r \in 2avSent[self] : r.val # mc.val}
                   \cup {[val |-> mc.val, bal |-> b]}
                  \in SUBSET [val : Value, bal : Ballot]
            BY <6>1, <5>1, mc.val \in Value  DEF 1cMessage
          <6>3. QED
            BY <4>1 , <6>2 DEF Inv, TypeOK
        <5>5. TypeOK!3' /\ TypeOK!4' /\ TypeOK!5'
          BY DEF Inv, TypeOK, Phase2av
        <5>6. TypeOK!6'
          <6>1. mb \in 2avMessage
            BY <5>2 DEF 2avMessage, ByzAcceptor
          <6>2. QED
            BY <4>1, <6>1 DEF Inv, TypeOK, BMessage
        <5>7. QED
          BY <5>3, <5>4, <5>5, <5>6 DEF TypeOK
      <4>6. bmsgsFinite'
         BY <4>1, FiniteMsgsLemma DEF Inv, bmsgsFinite
      <4>7. 1bInv1'
         <5>1. SUFFICES ASSUME NEW m \in bmsgs',
                               1bInv1!(m)!1
                        PROVE  1bInv1!(m)!2'
          BY DEF 1bInv1
        <5>2. m # mb
          BY <5>1 , mb.type = "2av"
        <5>3. m \in bmsgs
          BY <4>1, <5>2 DEF Phase2av
        <5>4. QED
          BY <5>1, <5>3, <4>4 DEF Phase2av, Inv, 1bInv1
      <4>8. 1bInv2'
        <5>1. SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                              1bInv2!(m1, m2)!1
                       PROVE  1bInv2!(m1, m2)!2'
          BY DEF 1bInv2
        <5>2. m1 # mb /\ m2 # mb
          BY <5>1 , mb.type = "2av"
        <5>3. m1 \in bmsgs /\ m2 \in bmsgs
          BY <4>1, <5>2
        <5>4. QED
          BY <5>1, <5>3 DEF Inv, 1bInv2
      <4>9. maxBalInv'
        <5>1. SUFFICES ASSUME NEW m \in bmsgs',
                              m.type \in {"1b", "2av", "2b"},
                              m.acc \in Acceptor
                       PROVE  m.bal =< maxBal'[m.acc]
          BY DEF maxBalInv
        <5>2. /\ \A x, y, z \in Ballot \cup {-1} :
                   (x =< y) /\ (y =< z) => (x =< z)
              /\ \A x \in Ballot \cup {-1} : x =< x
          BY SimpleArithmetic DEF Ballot
        <5>3. ASSUME NEW a \in Acceptor
              PROVE  /\ maxBal[a] =< maxBal'[a]
                     /\ maxBal[a] \in Ballot \cup {-1}
                     /\ maxBal'[a] \in Ballot \cup {-1}
          <6>1. <5>3!2!2 /\ <5>3!2!3
            BY  DEF Inv, TypeOK, Phase2av
          <6>2. maxBal[a] =< maxBal'[a]
            <7>1. CASE a = self
              BY <6>1, <7>1 DEF Phase2av, Inv, TypeOK
            <7>2. CASE a # self
              BY <5>2, <7>2, <6>1 DEF Phase2av, Inv, TypeOK
            <7>3. QED
              BY <7>1, <7>2
          <6>3. QED
            BY <6>1, <6>2
        <5>4. CASE m \in bmsgs
          <6>1. m.bal =< maxBal[m.acc]
            BY <5>1, <5>4 DEF Inv, maxBalInv
          <6>2. m.bal \in  Ballot \cup {-1}
            <7>1. CASE m.type = "1b"
              BY <5>4, <7>1, BMessageLemma DEF Inv, TypeOK, 1bMessage
            <7>2. CASE m.type = "2av"
              BY <5>4, <7>2, BMessageLemma DEF Inv, TypeOK, 2avMessage
            <7>3. CASE m.type = "2b"
              BY <5>4, <7>3, BMessageLemma DEF Inv, TypeOK, 2bMessage
            <7>4. QED
              BY <7>1, <7>2, <7>3, <5>1
          <6>3. QED
            <7>1. /\ maxBal[m.acc] =< maxBal'[m.acc]
                  /\ maxBal[m.acc] \in Ballot \cup {-1}
                  /\ maxBal'[m.acc] \in Ballot \cup {-1}
              BY <5>1, <5>3
            <7>2. QED
             BY <6>1, <6>2, <7>1, <5>2
        <5>5. CASE m = mb
          <6>1. b =< b
            BY SimpleArithmetic DEF Ballot
          <6>2.QED
            <7>1. m.bal = b /\ m.acc = self
              BY <5>5
            <7>2. maxBal'[self] = b
              BY DEF Inv, TypeOK, Phase2av
            <7>3. QED
             BY <6>1, <7>1, <7>2 DEF Inv, TypeOK, Phase2av
        <5>6. QED
          BY <5>4, <5>5, <4>1
      <4>10. 2avInv1'
        <5>1. ASSUME NEW m1 \in bmsgs, NEW m2 \in bmsgs,
                             2avInv1!(m1, m2)!1
              PROVE  m1 = m2
          BY <5>1 DEF Inv, 2avInv1
        <5>2. ASSUME NEW m1 \in bmsgs',
                     2avInv1!(m1, mb)!1
              PROVE m1 = mb
          <6>1. SUFFICES ASSUME m1 # mb
                         PROVE  FALSE
            OBVIOUS
          <6>2. m1 \in bmsgs
            BY <6>1, <4>1
          <6>3.  PICK r \in 2avSent[self] : r.bal >= m1.bal
            BY <5>2, <6>2 DEF Inv, 2avInv2
          <6>4. r.bal < b
            BY DEF Phase2av
          <6>5. m1.bal \in Ballot \cup {-1}
            BY <5>2, <6>2 DEF Inv, TypeOK, 1bMessage
          <6>6. r \in [val : Value, bal : Ballot]
            BY DEF Inv, TypeOK
          <6>7. r.bal \in Ballot
              BY <6>6 DEF Inv, TypeOK
          <6>8. \A m1bal, maxcbalself \in Ballot \cup {-1} :
                    maxcbalself < b /\maxcbalself >=  m1bal
                       => m1bal # b
              BY SimpleArithmetic DEF Ballot
          <6>9. m1.bal # b
              BY <6>3, <6>4, <6>5, <6>7, <6>8
          <6>10. QED
              BY <5>2, <6>9
        <5>3. QED
          <6> SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                             2avInv1!(m1, m2)!1
                       PROVE  m1 = m2
             BY DEF 2avInv1
          <6>1. CASE m1 # mb /\ m2 # mb
             BY <6>1, <5>1, <4>1 \* DEF Phase2av
          <6>2. CASE m1 = mb
            BY <5>2, <6>2
          <6>3. CASE m2 = mb
            BY <5>2, <6>3
          <6>4. QED
            BY <6>1, <6>2, <6>3
      <4>11. 2avInv2'
        <5>1. SUFFICES ASSUME NEW m \in bmsgs',
                              2avInv2!(m)!1
                       PROVE  \E r \in 2avSent'[m.acc] : /\ r.val = m.val
                                                         /\ r.bal >= m.bal
          BY DEF 2avInv2
        <5>2. CASE m.acc = self
          <6>1. CASE m = mb
            <7> DEFINE r == [val |-> mc.val, bal |-> b]
            <7>1. r \in 2avSent'[self]
              BY <4>1 DEF Inv, TypeOK
            <7>2. b >= b
              BY SimpleArithmetic DEF Ballot
            <7>3. QED
              BY <7>1, <6>1, mb.bal = b, <7>2
          <6>2. CASE m # mb
            <7>1. m \in bmsgs
              BY <4>1, <6>2
            <7>2. PICK r \in 2avSent[m.acc] : /\ r.val = m.val
                                              /\ r.bal >= m.bal
              BY <5>1, <7>1 DEF Inv, 2avInv2
            <7>3. CASE r.val = mc.val
              <8>1. r.bal =< maxBal[self]
                BY <5>2 DEF Inv, accInv
              <8>2. b >= m.bal
                <9>1. \A rbal, mbal, maxbal \in Ballot \cup {-1} :
                         rbal >= mbal /\ rbal =< maxbal /\ maxbal =< b
                           => b >= mbal
                  BY SimpleArithmetic DEF Ballot
                <9>2. r.bal \in Ballot
                  <10>1. r \in [val : Value, bal : Ballot]
                   BY <5>2 DEF Inv, TypeOK
                  <10>2. QED
                    BY <10>1
                <9>3. maxBal[self] \in Ballot \cup {-1}
                  BY DEF Inv, TypeOK
                <9>4. m.bal \in Ballot
                  BY <5>1, <5>2, <7>1, BMessageLemma DEF Inv, TypeOK, 2avMessage
                <9>5. QED
                  BY <9>1, <9>2, <9>3, <9>4, <7>2, <8>1 DEF Phase2av
              <8> DEFINE rr == [val |-> mc.val, bal |-> b]
              <8> rr \in 2avSent'[m.acc]
                BY <4>1, <5>2 DEF Inv, TypeOK
              <8>3. WITNESS rr \in 2avSent'[m.acc]
              <8>4. QED
                BY <8>2, <7>2, <7>3
            <7>4. CASE r.val # mc.val
              BY <7>2, <4>1, <5>2, <7>4 DEF Inv, TypeOK
            <7>5. QED
              BY <7>3, <7>4
          <6>3. QED
            BY <6>1, <6>2
        <5>3. CASE m.acc # self
          <6>1. m \in bmsgs
            BY <5>3, mb.acc = self, <4>1
          <6>2. m.acc \in Acceptor
            BY BMessageLemma, <6>1, <5>1 DEF Inv, TypeOK, 2avMessage
          <6>3. 2avSent'[m.acc] = 2avSent[m.acc]
            BY <6>2, <4>1, <5>3 DEF Inv, TypeOK
          <6>4. PICK r \in 2avSent[m.acc] : /\ r.val = m.val
                                            /\ r.bal >= m.bal
            BY <6>1, <6>2, <5>1 DEF Inv, 2avInv2
          <6>5. QED
            BY <6>3, <6>4
        <5>4. QED
          BY <5>2, <5>3
      <4>12. 2avInv3'
        <5>1. SUFFICES ASSUME NEW m \in bmsgs',
                               2avInv3!(m)!1
                        PROVE  2avInv3!(m)!2'
          BY DEF 2avInv3
        <5>2. CASE m \in bmsgs
          BY <5>1, <5>2, <4>4 DEF Inv, 2avInv3
        <5>3. CASE m = mb
          <6>1. mc \in msgs
            BY <4>1 DEF sentMsgs, msgs, 1cmsgs, msgsOfType
          <6>2. mc \in msgs'
            BY <6>1, <4>4
          <6>3. mc.bal = m.bal /\ mc.val = m.val
            BY <5>3 DEF sentMsgs
          <6>4. mc = [type |-> "1c", bal |-> m.bal, val |-> m.val]
            BY <4>2, <6>3
          <6>5. QED
            BY <6>1, <6>4, <4>4
        <5>4. QED
          BY <5>2, <5>3, <4>1
      <4>13. accInv'
        <5>1. SUFFICES ASSUME NEW a \in Acceptor,
                              NEW r \in 2avSent'[a]
                       PROVE  /\ r.bal =< maxBal'[a]
                              /\ [type |-> "1c", bal |-> r.bal, val |-> r.val]
                                    \in msgs'
          BY DEF accInv
        <5>2. maxBal[a] =< maxBal'[a]
          <6>1. CASE a = self
            BY <6>1 DEF Inv, TypeOK, Phase2av
          <6>2. CASE a # self
            <7>1. \A mbal \in Ballot \cup {-1} : mbal =< mbal
              BY SimpleArithmetic DEF Ballot
            <7>2. QED
              BY <6>2, <7>1 DEF Inv, TypeOK, Phase2av
          <6>3. QED
            BY <6>1, <6>2
        <5>3. CASE r \in 2avSent[a]
          <6>1. /\ r.bal =< maxBal[a]
                /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
            BY <5>3, <4>4 DEF Inv, accInv
          <6>2. \A rbal, maxbal, maxbalp \in Ballot \cup {-1} :
                   rbal =< maxbal /\ maxbal =< maxbalp => rbal =< maxbalp
            BY SimpleArithmetic DEF Ballot
          <6>3. r.bal \in Ballot
            <7>1. r \in [val : Value, bal : Ballot]
              BY <5>3 DEF Inv, TypeOK
            <7>2. QED
              BY <7>1
          <6>4. /\ maxBal[a] \in Ballot \cup {-1}
                /\ maxBal'[a] \in Ballot \cup {-1}
            BY <4>5 DEF Inv, TypeOK
          <6>5. r.bal =< maxBal'[a]
            BY <6>1, <6>2, <6>3, <6>4, <5>2
          <6>6. QED
            BY <6>1, <6>5
        <5>4. CASE r \notin 2avSent[a]
          <6>1. a = self
            <7>1. 2avSent'[a] # 2avSent[a]
              BY <5>4
            <7>2. QED
              BY <4>1, <7>1 DEF Inv, TypeOK
          <6>2. r = [val |-> mc.val, bal |-> b]
            BY <6>1, <5>4, <4>1 DEF Inv, TypeOK

          <6>3. [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
            <7>1. /\ mc \in msgsOfType("1c")
                  /\ mc.bal = b
                  /\ KnowsSafeAt(self, mc.bal, mc.val)
              BY <4>1 DEF sentMsgs, msgsOfType
            <7>2. mc \in msgs'
              BY <7>1, <4>4 DEF msgs, 1cmsgs
            <7>3. mc = <6>3!1
              BY <4>2, <6>2, <4>1 DEF sentMsgs \* <7>4
            <7>4. QED
              BY <7>2, <7>3
          <6>4. /\ maxBal'[a] = b
                /\ r.bal = b
            BY <6>1, <6>2 DEF Phase2av, Inv, TypeOK
          <6>5. b =< b
            BY SimpleArithmetic DEF Ballot
          <6>6. QED
            BY <6>3, <6>4, <6>5
        <5>5. QED
          BY <5>3, <5>4
      <4>14. knowsSentInv'
        <5>1. msgsOfType("1b")' = msgsOfType("1b")
          <6>1. ASSUME NEW m \in msgsOfType("1b")
                PROVE  m \in msgsOfType("1b")'
            BY <4>1 DEF msgsOfType
          <6>2. ASSUME NEW m \in msgsOfType("1b")'
                PROVE  m \in msgsOfType("1b")
            BY m.type = "1b", mb.type = "2av", <4>1 DEF msgsOfType
          <6>3. QED
            BY <6>1, <6>2
        <5>2. QED
          BY <5>1 DEF Phase2av, Inv, knowsSentInv, msgsOfType
      <4>15. QED
      BY <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11, <4>12,
         <4>13, <4>14 DEF Inv
    <3>3. CASE Phase2b(self, b)
      <4> USE Phase2b(self, b)
      <4>1. PICK v \in Value :
              /\ \E Q \in ByzQuorum :
                    \A a \in Q :
                       \E m \in sentMsgs("2av", b) : /\ m.val = v
                                                     /\ m.acc = a
              /\ msgs' = msgs \cup
                            {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
              /\ bmsgs' = (bmsgs \cup
                     {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]})
              /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
        <5>1. MsgsLemma!2!3
          BY MsgsLemma DEF Inv
        <5>2. MsgsLemma!2!3!(self, b)
          BY <5>1
        <5> DEFINE exp(v) == MsgsLemma!2!3!(self, b)!2!(v)
        <5>3. SUFFICES \E v \in Value : exp(v)
          OBVIOUS
        <5>4. QED
          BY <5>2
      <4> DEFINE mb == [type |-> "2b", acc |-> self, bal |-> b, val |-> v]
      <4>2. TypeOK'
        <5>1. TypeOK!1' /\  TypeOK!3' /\  TypeOK!5'
          BY DEF Phase2b, Inv, TypeOK
        <5>2. TypeOK!2'
          BY DEF Inv, TypeOK, Phase2b
        <5>3. TypeOK!4'
          BY <4>1 DEF Inv, TypeOK
        <5>4. bmsgs' \subseteq BMessage
           BY <4>1 DEF Inv, TypeOK, BMessage, 2bMessage, ByzAcceptor
        <5>5. QED
          BY <5>1, <5>2, <5>3, <5>4 DEF TypeOK
      <4>3. bmsgsFinite'
         BY <4>1, FiniteMsgsLemma DEF Inv, bmsgsFinite
      <4>4. 1bInv1'
         <5>1. SUFFICES ASSUME NEW m \in bmsgs',
                               1bInv1!(m)!1
                        PROVE  1bInv1!(m)!2'
          BY DEF 1bInv1
        <5>2. m # mb
          BY <5>1 , mb.type = "2b"
        <5>3. m \in bmsgs
          BY <4>1, <5>2
        <5>4. QED
          BY <4>1, <5>1, <5>3 DEF Inv, 1bInv1
      <4>5. 1bInv2'
        <5>1. SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                              1bInv2!(m1, m2)!1
                       PROVE  1bInv2!(m1, m2)!2'
          BY DEF 1bInv2
        <5>2. m1 # mb /\ m2 # mb
          BY <5>1 , mb.type = "2b"
        <5>3. m1 \in bmsgs /\ m2 \in bmsgs
          BY <4>1, <5>2
        <5>4. QED
          BY <5>1, <5>3 DEF Inv, 1bInv2
      <4>6. maxBalInv'
        \* The following copied almost exactly from proof
        \* for Phase2b(self, b)
        <5>1. SUFFICES ASSUME NEW m \in bmsgs',
                              m.type \in {"1b", "2av", "2b"},
                              m.acc \in Acceptor
                       PROVE  m.bal =< maxBal'[m.acc]
          BY DEF maxBalInv
        <5>2. /\ \A x, y, z \in Ballot \cup {-1} :
                   (x =< y) /\ (y =< z) => (x =< z)
              /\ \A x \in Ballot \cup {-1} : x =< x
          BY SimpleArithmetic DEF Ballot
        <5>3. ASSUME NEW a \in Acceptor
              PROVE  /\ maxBal[a] =< maxBal'[a]
                     /\ maxBal[a] \in Ballot \cup {-1}
                     /\ maxBal'[a] \in Ballot \cup {-1}
          <6>1. <5>3!2!2 /\ <5>3!2!3
            BY <4>2 DEF Inv, TypeOK, Phase2b
          <6>2. maxBal[a] =< maxBal'[a]
            <7>1. CASE a = self
              BY <6>1, <7>1 DEF Phase2b, Inv, TypeOK
            <7>2. CASE a # self
              BY <5>2, <7>2, <6>1 DEF Phase2b, Inv, TypeOK
            <7>3. QED
              BY <7>1, <7>2
          <6>3. QED
            BY <6>1, <6>2
        <5>4. CASE m \in bmsgs
          <6>1. m.bal =< maxBal[m.acc]
            BY <5>1, <5>4 DEF Inv, maxBalInv
          <6>2. m.bal \in  Ballot \cup {-1}
            <7>1. CASE m.type = "1b"
              BY <5>4, <7>1, BMessageLemma DEF Inv, TypeOK, 1bMessage
            <7>2. CASE m.type = "2av"
              BY <5>4, <7>2, BMessageLemma DEF Inv, TypeOK, 2avMessage
            <7>3. CASE m.type = "2b"
              BY <5>4, <7>3, BMessageLemma DEF Inv, TypeOK, 2bMessage
            <7>4. QED
              BY <7>1, <7>2, <7>3, <5>1
          <6>3. QED
            <7>1. /\ maxBal[m.acc] =< maxBal'[m.acc]
                  /\ maxBal[m.acc] \in Ballot \cup {-1}
                  /\ maxBal'[m.acc] \in Ballot \cup {-1}
              BY <5>1, <5>3
            <7>2. QED
             BY <6>1, <6>2, <7>1, <5>2
        <5>5. CASE m = mb
          <6>1. b =< b
            BY SimpleArithmetic DEF Ballot
          <6>2.QED
            <7>1. m.bal = b /\ m.acc = self
              BY <5>5
            <7>2. maxBal'[self] = b
              BY DEF Inv, TypeOK, Phase2b
            <7>3. QED
             BY <6>1, <7>1, <7>2 DEF Inv, TypeOK, Phase2b
        <5>6. QED
          BY <5>4, <5>5, <4>1
      <4>7. 2avInv1'
        <5>1. SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                              2avInv1!(m1, m2)!1
                       PROVE  2avInv1!(m1, m2)!2'
          BY DEF 2avInv1
        <5>2. m1 # mb /\ m2 # mb
          BY <5>1 , mb.type = "2b"
        <5>3. m1 \in bmsgs /\ m2 \in bmsgs
          BY <4>1, <5>2
        <5>4. QED
          BY <5>1, <5>3 DEF Inv, 2avInv1
      <4>8. 2avInv2'
        <5>1. SUFFICES ASSUME NEW m \in bmsgs',
                              2avInv2!(m)!1
                       PROVE  \E r \in 2avSent'[m.acc] : /\ r.val = m.val
                                                         /\ r.bal >= m.bal
           BY DEF 2avInv2, Phase2b, Inv, TypeOK
        <5>2. m # mb
          BY <5>1 , mb.type = "2b"
        <5>3. m \in bmsgs
          BY <4>1, <5>2
        <5>4. 2avSent'[m.acc] = 2avSent[m.acc]
          BY <5>1  DEF Inv, TypeOK, Phase2b
        <5>5. QED
          BY <5>1, <5>3, <5>4 DEF Inv, 2avInv2 \* BY <5>4, <5>5
      <4>9. 2avInv3'
        <5>1. SUFFICES ASSUME NEW m \in bmsgs',
                              2avInv3!(m)!1
                       PROVE  2avInv3!(m)!2'
          BY DEF 2avInv3
        <5>2. m # mb
          BY <5>1 , mb.type = "2b"
        <5>3. m \in bmsgs
          BY <4>1, <5>2
        <5>4. QED
          BY <5>1, <5>3, <4>1 DEF Inv, 2avInv3
      <4>10. accInv'
        \* Proof copied with a few changes from that of Phase1b
        <5> SUFFICES ASSUME NEW a \in Acceptor,
                            NEW r \in 2avSent[a]
                     PROVE  /\ r.bal =< maxBal'[a]
                            /\ [type |-> "1c", bal |-> r.bal, val |-> r.val]
                                   \in msgs'
          BY DEF accInv, Phase2b
        <5>1. /\ r.bal =< maxBal[a]
              /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
          BY DEF Inv, accInv
        <5>2. [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs'
          BY <5>1, MsgsLemma DEF Inv
        <5>3. maxBal[a] =< maxBal'[a]
          <6>1. CASE a = self
            <7>1. \A maxbal \in Ballot \cup {-1} :
                     b > maxbal => maxbal =< b
              BY SimpleArithmetic DEF Ballot
            <7>2. QED
              BY <6>1, <7>1 DEF Phase2b, Inv, TypeOK
          <6>2. CASE a # self
            <7>1. \A maxbal \in Ballot \cup {-1} : maxbal =< maxbal
              BY SimpleArithmetic DEF Ballot
            <7>2. maxBal'[a] = maxBal[a]
              BY <6>2 DEF Phase2b, Inv, TypeOK
            <7>3. QED
              BY <7>1, <7>2 DEF Phase2b, Inv, TypeOK
          <6>3. QED
            BY <6>1, <6>2
        <5>4. r.bal =< maxBal'[a]
          <6>1. \A rbal, maxb, maxbp \in Ballot \cup {-1} :
                   rbal =< maxb /\ maxb =< maxbp =>  rbal =< maxbp
            BY SimpleArithmetic DEF Ballot
          <6>2. r.bal \in Ballot
            <7>1. 2avSent[a] \in SUBSET [val : Value, bal : Ballot]
              BY DEF Inv, TypeOK
            <7>2. r \in [val : Value, bal : Ballot]
              BY <7>1
            <7>3. QED
              BY <7>2
          <6>3. /\ maxBal[a] \in Ballot \cup {-1}
                /\ maxBal'[a] \in Ballot \cup {-1}
            BY <4>2 DEF Inv, TypeOK
          <6>4. QED
            BY <6>1, <6>2, <6>3, <5>1, <5>3
        <5>5. QED
          BY <5>2, <5>4
      <4>11. knowsSentInv'
        <5>1. msgsOfType("1b") \subseteq msgsOfType("1b")'
          BY <4>1 DEF Phase2b, msgsOfType
        <5>2. QED
          BY <5>1 DEF Inv, knowsSentInv, Phase2b
      <4>12. QED
      BY <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9,
         <4>10, <4>11 DEF Inv
    <3>4. CASE LearnsSent(self, b)
      <4> USE LearnsSent(self, b)
      <4>1. PICK MS : /\ MS \subseteq {m \in msgsOfType("1c") : m.bal = b}
                      /\ msgs' = msgs \cup MS
        BY MsgsLemma DEF Inv
      <4>2. PICK S :
              /\ S \subseteq sentMsgs("1b", b)
              /\ knowsSent' =
                  [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
        BY DEF LearnsSent
      <4>3. TypeOK'
        <5>1. knowsSent' \in [Acceptor -> SUBSET 1bMessage]
          <6> DEFINE ks(a) == IF a = self THEN knowsSent[self] \cup S
                                          ELSE knowsSent[a]
          <6> SUFFICES ASSUME NEW a \in Acceptor
                       PROVE  ks(a) \in SUBSET 1bMessage
            BY <4>2 DEF Inv, TypeOK
          <6>1. CASE a # self
            BY <6>1 DEF Inv, TypeOK
          <6>2. CASE a = self
            <7> SUFFICES ASSUME NEW m \in S
                         PROVE  m \in 1bMessage
              BY <6>2 DEF Inv, TypeOK
            <7> QED
              BY <4>2, BMessageLemma DEF sentMsgs, Inv, TypeOK
          <6>3. QED
            BY <6>1, <6>2
        <5>2. QED
          BY <5>1 DEF Inv, TypeOK, LearnsSent
      <4>4. bmsgsFinite'
        BY DEF LearnsSent, Inv, bmsgsFinite, 1bOr2bMsgs
      <4>5. 1bInv1'
        BY <4>1 DEF LearnsSent, Inv, 1bInv1
      <4>6. 1bInv2'
        BY DEF LearnsSent, Inv, 1bInv2
      <4>7. maxBalInv'
        BY DEF LearnsSent, Inv, maxBalInv
      <4>8. 2avInv1'
        BY DEF LearnsSent, Inv, 2avInv1
      <4>9. 2avInv2'
        BY DEF LearnsSent, Inv, 2avInv2
      <4>10. 2avInv3'
        BY <4>1 DEF LearnsSent, Inv, 2avInv3
      <4>11. accInv'
        BY <4>1 DEF LearnsSent, Inv, accInv
      <4>12. knowsSentInv'
        <5> SUFFICES ASSUME NEW a \in Acceptor
                     PROVE  knowsSent'[a] \subseteq msgsOfType("1b")
          BY DEF LearnsSent, knowsSentInv, msgsOfType
        <5>1. CASE a # self
          BY <4>2 DEF Inv, TypeOK, knowsSentInv, sentMsgs, msgsOfType
        <5>2. CASE a = self
          BY <4>2 DEF Inv, TypeOK, knowsSentInv, sentMsgs, msgsOfType
        <5>3. QED
          BY <5>1, <5>2
      <4>13. QED
        BY <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10,
         <4>11, <4>12 DEF Inv
    <3>5. QED
      BY <2>1, <3>1, <3>2, <3>3, <3>4
  <2>2. ASSUME NEW self \in Ballot,
               \/ Phase1a(self)
               \/ Phase1c(self)
        PROVE  Inv'
    <3>1. CASE Phase1a(self)
      <4> USE Phase1a(self)
      <4> DEFINE ma == [type |-> "1a", bal |-> self]
      <4>1. msgs' = msgs \cup {ma}
        BY MsgsLemma DEF Inv
      <4>2. TypeOK'
        <5>1. bmsgs' \subseteq BMessage
          BY DEF Phase1a, Inv, TypeOK, BMessage, 1aMessage
        <5>2. QED
          BY <5>1 DEF Inv, TypeOK, Phase1a
      <4>3. bmsgsFinite'
        BY FiniteMsgsLemma DEF Inv, bmsgsFinite, Phase1a
      <4>4. 1bInv1'
        BY <4>1 DEF Phase1a, Inv, 1bInv1
      <4>5. 1bInv2'
        <5>1. SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                              1bInv2!(m1, m2)!1
                       PROVE  1bInv2!(m1, m2)!2'
          BY DEF 1bInv2
        <5>2. m1 # ma /\ m2 # ma
          BY <5>1 , ma.type = "1a"
        <5>3. m1 \in bmsgs /\ m2 \in bmsgs
          BY  <5>2 DEF Phase1a
        <5>4. QED
          BY <5>1, <5>3 DEF Inv, 1bInv2
      <4>6. maxBalInv'
        BY DEF Phase1a, Inv, maxBalInv
      <4>7. 2avInv1'
        <5>1. SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                              2avInv1!(m1, m2)!1
                       PROVE  2avInv1!(m1, m2)!2'
          BY DEF 2avInv1
        <5>2. m1 # ma /\ m2 # ma
          BY <5>1 , ma.type = "1a"
        <5>3. m1 \in bmsgs /\ m2 \in bmsgs
          BY <5>2 DEF Phase1a
        <5>4. QED
          BY <5>1, <5>3 DEF Inv, 2avInv1
      <4>8. 2avInv2'
        BY DEF Phase1a, Inv, 2avInv2
      <4>9. 2avInv3'
        BY <4>1 DEF Phase1a, Inv, 2avInv3
      <4>10. accInv'
        BY <4>1 DEF Phase1a, Inv, accInv
      <4>11. knowsSentInv'
        BY  DEF Inv, knowsSentInv, msgsOfType, Phase1a
      <4>12. QED
        BY <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9,
           <4>10, <4>11 DEF Inv
    <3>2. CASE Phase1c(self)
      <4> USE Phase1c(self)
      <4>1. PICK S : /\ S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]
                     /\ bmsgs' = bmsgs \cup S
        BY DEF Phase1c
      <4>2. PICK MS :
               /\ MS \in SUBSET [type : {"1c"}, bal : {self}, val : Value]
               /\ \A m \in MS :
                    \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)
               /\ msgs' = msgs \cup MS
        BY MsgsLemma DEF Inv
      <4>3. TypeOK'
        <5>1. bmsgs' \subseteq BMessage
          BY <4>1 DEF Inv, TypeOK, BMessage, 1cMessage
        <5>2. QED
          BY <5>1 DEF Inv, TypeOK, Phase1c
      <4>4. bmsgsFinite'
        <5>1. 1bOr2bMsgs' = 1bOr2bMsgs
          BY <4>1 DEF 1bOr2bMsgs
        <5>2. QED
          BY <5>1 DEF bmsgsFinite, Inv
      <4>5. 1bInv1'
        BY <4>2 DEF Phase1c, Inv, 1bInv1
      <4>6. 1bInv2'
        <5>1. SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                              1bInv2!(m1, m2)!1
                       PROVE  1bInv2!(m1, m2)!2'
          BY DEF 1bInv2
        <5>2. m1 \notin S /\ m2 \notin S
          <6>1. \A m \in S : m.type = "1c"
            BY <4>1
          <6>2. QED
            BY <6>1, <5>1
        <5>3. m1 \in bmsgs /\ m2 \in bmsgs
          BY  <5>2, <4>1
        <5>4. QED
          BY <5>1, <5>3 DEF Inv, 1bInv2
      <4>7. maxBalInv'
        BY DEF Phase1c, Inv, maxBalInv
      <4>8. 2avInv1'
        <5>1. SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                              2avInv1!(m1, m2)!1
                       PROVE  2avInv1!(m1, m2)!2'
          BY DEF 2avInv1
        <5>2. m1 \notin S /\ m2 \notin S
          <6>1. \A m \in S : m.type = "1c"
            BY <4>1
          <6>2. QED
            BY <6>1, <5>1
        <5>3. m1 \in bmsgs /\ m2 \in bmsgs
          BY  <5>2, <4>1
        <5>4. QED
          BY <5>1, <5>3 DEF Inv, 2avInv1
      <4>9. 2avInv2'
        BY DEF Phase1c, Inv, 2avInv2
      <4>10. 2avInv3'
        BY <4>2 DEF Phase1c, Inv, 2avInv3
      <4>11. accInv'
        BY <4>2 DEF Phase1c, Inv, accInv
      <4>12. knowsSentInv'
        BY  DEF Inv, knowsSentInv, msgsOfType, Phase1c
      <4>13. QED
        BY <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10,
           <4>11, <4>12 DEF Inv
    <3>3. QED
      BY <3>1, <3>2, <2>2
  <2>3. ASSUME NEW self \in FakeAcceptor,
               FakingAcceptor(self)
        PROVE
         Inv'
    <3> USE FakingAcceptor(self)
    <3>1. PICK m \in 1bMessage \cup 2avMessage \cup 2bMessage :
                 /\ m.acc \notin Acceptor
                 /\ bmsgs' = bmsgs \cup {m}
      BY BQA DEF FakingAcceptor
    <3>2. msgs' = msgs
      BY MsgsLemma DEF Inv
    <3>3. TypeOK'
      BY <3>1 DEF Inv, TypeOK, BMessage, FakingAcceptor
    <3>4. bmsgsFinite'
      BY <3>1, FiniteMsgsLemma DEF Inv, TypeOK
    <3>5. 1bInv1'
      <4>1. SUFFICES ASSUME NEW mm \in bmsgs',
                            1bInv1!(mm)!1
                     PROVE  1bInv1!(mm)!2'
        BY DEF 1bInv1
      <4>2.mm \in bmsgs
        BY <4>1, <3>1
      <4>3. QED
        BY <4>1, <4>2, <3>2 DEF Inv, 1bInv1
    <3>6. 1bInv2'
      <4>1. SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                            1bInv2!(m1,m2)!1
                     PROVE  m1 = m2
        BY DEF 1bInv2
      <4>2.m1 \in bmsgs /\ m2 \in bmsgs
        BY <4>1, <3>1
      <4>3. QED
        BY <4>1, <4>2 DEF Inv, 1bInv2
    <3>7. maxBalInv'
      <4>1. SUFFICES ASSUME NEW mm \in bmsgs',
                            maxBalInv!(mm)!1
                     PROVE  maxBalInv!(mm)!2'
        BY DEF maxBalInv
      <4>2.mm \in bmsgs
        BY <4>1, <3>1
      <4>3. QED
        BY <4>1, <4>2 DEF Inv, maxBalInv, FakingAcceptor
    <3>8. 2avInv1'
      <4>1. SUFFICES ASSUME NEW m1 \in bmsgs', NEW m2 \in bmsgs',
                            2avInv1!(m1,m2)!1
                     PROVE  m1 = m2
        BY DEF 2avInv1
      <4>2.m1 \in bmsgs /\ m2 \in bmsgs
        BY <4>1, <3>1
      <4>3. QED
        BY <4>1, <4>2 DEF Inv, 2avInv1
    <3>9. 2avInv2'
      <4>1. SUFFICES ASSUME NEW mm \in bmsgs',
                            2avInv2!(mm)!1
                     PROVE  2avInv2!(mm)!2'
        BY DEF 2avInv2
      <4>2.mm \in bmsgs
        BY <4>1, <3>1
      <4>3. QED
        BY <4>1, <4>2 DEF Inv, 2avInv2, FakingAcceptor
    <3>10. 2avInv3'
      <4>1. SUFFICES ASSUME NEW mm \in bmsgs',
                            2avInv3!(mm)!1
                     PROVE  2avInv3!(mm)!2'
        BY DEF 2avInv3
      <4>2.mm \in bmsgs
        BY <4>1, <3>1
      <4>3. QED
        BY <4>1, <4>2, <3>2 DEF Inv, 2avInv3
    <3>11. accInv'
      BY <3>2 DEF Inv, accInv, FakingAcceptor
    <3>12. knowsSentInv'
      <4> SUFFICES ASSUME NEW a \in Acceptor
                   PROVE  knowsSent'[a] \subseteq msgsOfType("1b")'
        BY DEF knowsSentInv
      <4>1. msgsOfType("1b") \subseteq msgsOfType("1b")'
        BY <3>1 DEF msgsOfType
      <4>2. QED
        BY <4>1 DEF FakingAcceptor, Inv, knowsSentInv
    <3>13. QED
      BY <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10,
         <3>11, <3>12 DEF Inv
  <2>4. ASSUME UNCHANGED vars
        PROVE  Inv'
    <3> USE UNCHANGED vars DEF Inv, vars
    <3> msgs = msgs'
      BY DEF msgs, msgsOfType, 1bmsgs, 1bRestrict, acceptorMsgsOfType, 1cmsgs,
       KnowsSafeAt, 2amsgs
    <3> QED
      BY DEF TypeOK, bmsgsFinite, 1bOr2bMsgs, 1bInv1, 1bInv2,
         maxBalInv, 2avInv1, 2avInv2, 2avInv3, accInv, knowsSentInv, msgsOfType
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4, NextDef

<1>3. QED
  (*************************************************************************)
  (* BY <1>1, <1>2, RuleInv1 DEF Spec                                      *)
  (*************************************************************************)
  PROOF OMITTED
-----------------------------------------------------------------------------
(***************************************************************************)
(* We next use the invariance of Inv to prove that algorithm BPCon         *)
(* implements algorithm PCon under the refinement mapping                  *)
(* defined by the INSTANCE statement above.  Again, we must omit the       *)
(* trivial temporal logic proofs until temporal logic reasoning is         *)
(* implemented in TLAPS.                                                   *)
(***************************************************************************)
THEOREM Spec => P!Spec
<1>1. Init => P!Init
  <2> SUFFICES ASSUME Init
               PROVE  P!Init
    OBVIOUS
  <2>1. MaxBallot({}) = -1
    BY MaxBallotProp, EmptySetFinite
  <2>2. P!Init!1
    BY <2>1 DEF Init, PmaxBal, 1bOr2bMsgs
  <2>3. P!Init!2 /\ P!Init!3
    BY DEF Init, None, P!None
  <2>4. msgs = {}
    <3>1. msgsOfType("1a") = {} /\ acceptorMsgsOfType("2b") = {}
      BY DEF Init, msgsOfType, acceptorMsgsOfType
    <3>2. 1bmsgs = {} /\ 1cmsgs = {}
      BY DEF Init, msgsOfType, acceptorMsgsOfType, 1bmsgs, 1cmsgs
    <3>3. 2amsgs = {}
      <4>1. {} \notin Quorum
        BY BQA DEF Quorum
      <4>2. acceptorMsgsOfType("2av") = {}
        BY DEF Init, msgsOfType, acceptorMsgsOfType
      <4> QED
        BY <4>1, <4>2 DEF 2amsgs
    <3>4. QED
      BY <3>1, <3>2, <3>3 DEF msgs
  <2>5. QED
    BY <2>2, <2>3, <2>4 DEF  P!Init

<1>2. Inv /\ Inv' /\ [Next]_vars => [P!Next]_P!vars
  <2> InvP == Inv'  \* We probably don't need to assume Inv'
  <2>1. UNCHANGED vars => UNCHANGED P!vars
    <3> SUFFICES ASSUME UNCHANGED vars
        PROVE UNCHANGED P!vars
      OBVIOUS
    <3>1. UNCHANGED <<maxVBal, maxVVal>>
      BY DEF vars
    <3>2. UNCHANGED PmaxBal
      BY DEF vars, PmaxBal, 1bOr2bMsgs
    <3>3. UNCHANGED msgs
      <4> USE DEF vars
      <4>1. UNCHANGED <<msgsOfType("1a"), acceptorMsgsOfType("2b"), 1bmsgs>>
        BY DEF msgsOfType, acceptorMsgsOfType, 1bmsgs, 2amsgs
      <4>2. UNCHANGED 1cmsgs
        BY DEF 1cmsgs, msgsOfType, KnowsSafeAt
      <4>3. UNCHANGED 2amsgs
        BY DEF 2amsgs, msgsOfType, acceptorMsgsOfType
      <4>4. QED
        BY <4>1, <4>2,  <4>3  DEF msgs
    <3>4. QED
      BY <3>1, <3>2, <3>3 DEF P!vars
  <2> SUFFICES ASSUME Inv, InvP, Next
               PROVE  P!TLANext \/ P!vars' = P!vars
    <3>1. Inv /\ [Next]_vars => Inv /\ [Next]_vars
      BY DEF Inv
    <3>2. UNCHANGED vars => UNCHANGED P!vars
       <4> HAVE UNCHANGED vars
       <4> USE DEF vars
       <4>1. UNCHANGED PmaxBal
         BY DEF PmaxBal, 1bOr2bMsgs
       <4>2. UNCHANGED msgs
         <5>1. /\ UNCHANGED msgsOfType("1a")
               /\ UNCHANGED acceptorMsgsOfType("2b")
           BY DEF msgsOfType, acceptorMsgsOfType
         <5>2. UNCHANGED 1bmsgs
           BY DEF 1bmsgs, msgsOfType, acceptorMsgsOfType
         <5>3. UNCHANGED 1cmsgs
           BY DEF 1cmsgs, msgsOfType, KnowsSafeAt
         <5>4. UNCHANGED 2amsgs
           BY DEF 2amsgs, msgsOfType, acceptorMsgsOfType
         <5>5. QED
         BY <5>1, <5>2, <5>3, <5>4 DEF msgs
       <4>3. QED
         BY <4>1, <4>2 DEF  P!vars, PmaxBal, 1bOr2bMsgs
    <3>3. Inv /\ P!TLANext => P!Next
      BY <3>1, <3>2, PNextDef
      DEF Inv, P!ProcSet, P!Init, Ballot, P!Ballot
    <3> QED
    BY <3>1, <3>2, <3>3, P!NextDef, NextDef DEF Inv
  <2> HIDE DEF InvP
  <2>2. \A a \in Acceptor : PmaxBal[a] \in Ballot \cup {-1}
    <3> SUFFICES ASSUME NEW a \in Acceptor
                 PROVE  PmaxBal[a] \in Ballot \cup {-1}
      OBVIOUS
    <3> DEFINE S == {m.bal : m \in {ma \in bmsgs :
                                           /\ ma.type \in {"1b", "2b"}
                                           /\ ma.acc = a}}
    <3>1. PmaxBal[a] = MaxBallot(S)
      BY DEF PmaxBal, 1bOr2bMsgs
    <3>2. /\ IsFiniteSet(S)
          /\ S \in SUBSET Ballot
      BY PMaxBalLemma3 DEF Inv
    <3>3. CASE S = {}
      BY <3>1, <3>2, <3>3, MaxBallotProp
    <3>4. CASE S # {}
      BY <3>1, <3>2, <3>4, MaxBallotProp
    <3>5. QED
      BY <3>3, <3>4
  <2>3. ASSUME NEW self \in Acceptor, NEW b \in Ballot,
               Phase1b(self, b)
        PROVE  P!TLANext \/ P!vars' = P!vars
    <3>1. /\ P!sentMsgs("1a", b) # {}
          /\ msgs' = msgs \cup {[type |-> "1b", acc |-> self, bal |-> b,
                         mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
      <4>1. <3>1!2
        BY <2>3, MsgsLemma DEF Inv
      <4>2. PICK m \in sentMsgs("1a", b) : m.type = "1a" /\ m.bal = b
        BY <2>3 DEF Phase1b, sentMsgs
      <4>3. m \in msgsOfType("1a")
        BY <4>2 DEF sentMsgs, msgsOfType
      <4>4. m \in msgs
        BY <4>3 DEF msgs
      <4>5. m \in P!sentMsgs("1a", b)
        BY <4>4, <4>2 DEF P!sentMsgs
      <4>6. QED
        BY <4>1, <4>5
    <3>2. UNCHANGED <<maxVBal, maxVVal>>
      BY <2>3 DEF Phase1b
    <3>3. /\ b > PmaxBal[self]
          /\ PmaxBal' = [PmaxBal EXCEPT ![self] = b]
      <4>1. b > PmaxBal[self]
        <5>1. b > maxBal[self]
          BY <2>3 DEF Phase1b
        <5>2. maxBal[self] \in Ballot \cup {-1}
          BY DEF Inv, TypeOK
        <5>3. \A pmb, mb \in Ballot \cup {-1} :
                  b > mb /\ pmb =< mb => b > pmb
          BY SimpleArithmetic DEF Ballot
        <5>4. QED
          BY <5>1, <5>2, <5>3, PmaxBalLemma4, <2>2 DEF Inv
      <4> DEFINE m == [type  |-> "1b", bal |-> b, acc |-> self,
                       m2av |-> 2avSent[self],
                       mbal |-> maxVBal[self], mval |-> maxVVal[self]]
                 mA(a) == {ma \in bmsgs : /\ ma.type \in {"1b", "2b"}
                                          /\ ma.acc = a}
                 S(a) == {ma.bal : ma \in mA(a)}
      <4>2. bmsgs' = bmsgs \cup {m}
        BY <2>3 DEF Phase1b
      <4>3. mA(self)' = mA(self) \cup {m}
        <5>1. mA(self)' = mA(self) \cup {ma \in {m} : /\ ma.type \in {"1b", "2b"}
                                                      /\ ma.acc = self}
          BY <4>2
        <5>2. m.type = "1b" /\ m.acc = self
          OBVIOUS
        <5>3. \A ma \in {m} : ma.type = "1b" /\ ma.acc = self
          BY <5>2
        <5>4. QED
          BY <5>1, <5>3
      <4>4. /\ PmaxBal = [a \in Acceptor |-> MaxBallot(S(a))]
            /\ PmaxBal' = [a \in Acceptor |-> MaxBallot(S(a))']
        BY DEF PmaxBal, 1bOr2bMsgs
      <4> HIDE DEF mA
      <4>5. S(self)' = S(self) \cup {b}
        BY <4>3, m.bal = b
      <4>6. MaxBallot(S(self) \cup {b}) = b
        <5>1. b > MaxBallot(S(self))
          BY <4>1, <4>4
        <5> DEFINE SS == S(self) \cup {b}
        <5>2. b \in SS
          OBVIOUS
        <5>3. IsFiniteSet(S(self))
          <6>1. IsFiniteSet(1bOr2bMsgs)
            BY DEF Inv, bmsgsFinite
          <6>2. IsFiniteSet(mA(self))
            BY <6>1, SubsetOfFiniteSetFinite DEF mA, 1bOr2bMsgs
          <6> DEFINE f[ma \in mA(self)] == ma.bal
          <6>3. S(self) = {f[ma] : ma \in mA(self)}
            OBVIOUS
          <6> HIDE DEF f
          <6>4. QED
            BY <6>2, <6>3, ImageOfFiniteSetFinite
        <5>4. IsFiniteSet(SS)
          BY <5>3, SingletonSetFinite, UnionOfFiniteSetsFinite
        <5>5. SS \subseteq Ballot \cup {-1}
          <6>1. ASSUME NEW mm \in mA(self)
                PROVE  mm.bal \in Ballot \cup {-1}
            <7>1. mm \in bmsgs /\ mm.type \in {"1b", "2b"}
              BY DEF mA
            <7>2. CASE mm.type = "1b"
              BY <7>1, <7>2, BMessageLemma DEF Inv, TypeOK, 1bMessage
            <7>3. CASE mm.type = "2b"
              BY <7>1, <7>2, BMessageLemma DEF Inv, TypeOK, 2bMessage
            <7>4. QED
              BY <7>1, <7>2, <7>3
          <6>2. QED
            BY <6>1
        <5>6. \A x \in SS : b >= x
          <6>1. b >= b
            BY SimpleArithmetic DEF Ballot
          <6>2. SUFFICES ASSUME NEW x \in S(self)
                         PROVE b >= x
            BY <6>1
          <6>3. S(self) # {}
            OBVIOUS
          <6> HIDE DEF S
          <6>4. /\ MaxBallot(S(self)) \in S(self)
                /\ MaxBallot(S(self)) >= x
            BY <5>3, <5>5, <6>3, MaxBallotProp, IsFiniteSet(S(self))
          <6>5. b > MaxBallot(S(self))
            BY <5>1, <4>4
          <6>6. /\ MaxBallot(S(self)) \in Ballot \cup {-1}
                /\ x \in Ballot \cup {-1}
            BY <5>5, <6>4
          <6>7. \A mbs\in Ballot \cup {-1} :
                    b > mbs /\ mbs >= x => b >= x
            BY <6>6, SimpleArithmetic DEF Ballot
          <6>8. QED
            BY <5>1, <6>4, <6>6, <6>7
        <5>7. QED
          <6> HIDE DEF SS
          <6>1. b = MaxBallot(SS)
            BY <5>2, <5>4, <5>5, <5>6,  MaxBallotLemma1
          <6>2. QED
            BY <6>1 DEF SS
      <4>7. \A a \in Acceptor : a # self => S(a)' = S(a)
        <5> USE DEF mA
        <5>1. SUFFICES ASSUME NEW a \in Acceptor, a # self
                       PROVE  S(a)' = S(a)
          OBVIOUS
        <5>2. m.acc # a
          BY <5>1
        <5>3. mA(a)' = mA(a)
          <6>1. ASSUME NEW mm \in mA(a)'
                PROVE  mm \in mA(a)
            BY <4>2, <5>2, mm.acc = a  \* <7>3
          <6>2. ASSUME NEW mm \in mA(a)
                PROVE  mm \in mA(a)'
             BY <4>2
          <6>3. QED
            BY <6>1, <6>2
        <5>4. QED
          BY <5>3

      <4>8. PmaxBal' = [PmaxBal EXCEPT ![self] = b]
        <5>1. SUFFICES ASSUME  NEW a \in Acceptor
                       PROVE    PmaxBal'[a] = IF a = self THEN b
                                                          ELSE PmaxBal[a]
          BY DEF PmaxBal, 1bOr2bMsgs
        <5>2. (a # self) => MaxBallot(S(a))' = MaxBallot(S(a))
          BY <4>7
        <5>3. (a # self) => PmaxBal'[a] = PmaxBal[a]
          BY <4>4, <4>7, <5>2  DEF PmaxBal, 1bOr2bMsgs
        <5> QED
        BY <5>2, <4>4, <4>5, <4>6
      <4>9. QED
        BY <4>1, <4>8
    <3> DEFINE m == [type |-> "1b", acc |-> self, bal |-> b,
                     mbal |-> maxVBal[self], mval |-> maxVVal[self]]
    <3>4. QED
       BY <3>1, <3>2, <3>3 DEF P!TLANext, P!Ballot, Ballot, P!Phase1b
  <2>4. ASSUME NEW self \in Acceptor, NEW b \in Ballot,
               Phase2av(self, b)
        PROVE  P!TLANext \/ P!vars' = P!vars
    <3>1. PmaxBal' = PmaxBal
      <4> DEFINE mm(m) == [type |-> "2av", bal |-> b,
                           val |-> m.val, acc |-> self]
      <4>1. PICK m : bmsgs' = bmsgs \cup {mm(m)}
        BY <2>4  DEF Phase2av
      <4>2. mm(m).type = "2av"
        OBVIOUS
      <4> QED
         BY <4>1, <4>2, PmaxBalLemma1
    <3>2. CASE msgs' = msgs
       BY <3>1, <3>2, <2>4 DEF Phase2av, P!vars
    <3>3. CASE /\ msgs' # msgs
               /\ \E v \in Value :
                    /\ [type |-> "1c", bal |-> b, val |-> v] \in msgs
                    /\ msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]}
      <4>1. PICK v \in Value :
                 /\ [type |-> "1c", bal |-> b, val |-> v] \in msgs
                 /\ msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]}
        BY <3>3
      <4>2. P!sentMsgs("2a", b) = {}
        <5> DEFINE m2a == [type |-> "2a", bal |-> b, val |-> v]

        <5>1. SUFFICES ASSUME NEW m \in P!sentMsgs("2a", b)
                       PROVE  m = m2a
          <6>1. \A m \in P!sentMsgs("2a", b) : m \in msgs
            BY DEF P!sentMsgs
          <6>2. QED
          BY <3>3, <4>1, <6>1
        <5>2. /\ m \in 2amsgs
              /\ m.type = "2a"
              /\ m.bal = b
          BY MsgsTypeLemma DEF P!sentMsgs
        <5>3. PICK Q \in Quorum :
                     \A a \in Q :
                       \E mav \in acceptorMsgsOfType("2av") :
                         /\ mav.acc = a
                         /\ mav.bal = b
                         /\ mav.val = m.val
          BY <5>2 DEF 2amsgs
        <5>4. PICK Q2 \in Quorum :
                     \A a \in Q2 :
                       \E m2av \in acceptorMsgsOfType("2av")' :
                         /\ m2av.acc = a
                         /\ m2av.bal = b
                         /\ m2av.val = v
           <6>1. /\ m2a.type = "2a"
                 /\ m2a.bal = b
                 /\ m2a.val = v
             OBVIOUS
           <6>2. m2a \in 2amsgs'
             BY <4>1, <6>1, m2a \in msgs', MsgsTypeLemmaPrime
           <6> HIDE DEF m2a
           <6>3. QED
            BY <6>1, <6>2 DEF 2amsgs
        <5>5. PICK a \in Q \cap Q2 : a \in Acceptor
          BY QuorumTheorem
        <5>6. PICK mav \in acceptorMsgsOfType("2av") :
                         /\ mav.acc = a
                         /\ mav.bal = b
                         /\ mav.val = m.val
          BY <5>3, <5>5
        <5>7. PICK m2av \in acceptorMsgsOfType("2av")' :
                      /\ m2av.acc = a
                      /\ m2av.bal = b
                      /\ m2av.val = v
          BY <5>4, <5>5
        <5>8. mav \in acceptorMsgsOfType("2av")'
          BY <2>4 DEF acceptorMsgsOfType, msgsOfType, Phase2av
        <5>9. m2av = mav
          BY <5>5, <5>6, <5>7, <5>8 DEF 2avInv1 , InvP, Inv, acceptorMsgsOfType, msgsOfType
        <5>10. m = [type |-> "2a", bal |-> b, val |-> m.val]
          BY <5>2 DEF 2amsgs
        <5>11. QED
          BY <5>6, <5>7, <5>9, <5>10
      <4>3. P!Phase2a(b, v)
        BY <2>4, <3>1, <4>1, <4>2 DEF P!Phase2a, Phase2av
      <4>4. QED
        BY <4>3 DEF P!TLANext, Ballot, P!Ballot
    <3>0a. TypeOK
        BY Inv DEF Inv
    <3>0b.\/ msgs' = msgs
         \/ (/\ msgs' # msgs
             /\ \E v \in Value :
                    /\ [type |-> "1c", bal |-> b, val |-> v] \in msgs
                    /\ msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]})
         BY MsgsLemma, <2>4, <3>0a
    <3>4. QED
      BY <3>2, <3>3, <3>0b, <2>4 DEF Inv
  <2>5. ASSUME NEW self \in Acceptor, NEW b \in Ballot,
               Phase2b(self, b)
        PROVE  P!TLANext \/ P!vars' = P!vars
    <3> USE <2>5
    <3>1. b \geq PmaxBal[self]
      <4>1. PmaxBal[self] =< maxBal[self]
        BY PmaxBalLemma4 DEF Inv
      <4>2. maxBal[self] =< b
        BY DEF Phase2b
      <4>3. \A pmb, mb \in Ballot \cup {-1} :
                pmb =< mb /\ mb =< b =>  b \geq pmb
        BY SimpleArithmetic DEF Ballot
      <4>4. QED
        BY <4>1, <4>2, <4>3, PmaxBalLemma5 DEF Inv, TypeOK
    <3>2. PICK v \in Value :
                 /\ \E Q \in ByzQuorum :
                      \A a \in Q :
                        \E m \in sentMsgs("2av", b) : /\ m.val = v
                                                      /\ m.acc = a
                 /\ msgs' = msgs \cup
                            {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
                 /\ bmsgs' = bmsgs \cup
                            {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]}
                 /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
      <4>1. MsgsLemma!2!3
         BY MsgsLemma DEF Inv
      <4>2. MsgsLemma!2!3!(self,b)!2
        BY <4>1
      <4>3. QED
        BY <4>2
    <3> DEFINE m == [type |-> "2a", bal |-> b, val |-> v]
               m2b == [type |-> "2b", acc |-> self, bal |-> b, val |-> v]
    <3>3. m \in P!sentMsgs("2a", b)
      <4>1. m \in 2amsgs
        <5>1. m \in [type : {"2a"}, bal : Ballot, val : Value]
          OBVIOUS
        <5>2. PICK Q \in Quorum :
                     \A a \in Q :
                        \E mm \in sentMsgs("2av", b) : /\ mm.val = v
                                                       /\ mm.acc = a
         <6>1. \A BQ \in ByzQuorum : \E Q \in Quorum : Q \subseteq BQ
           BY DEF Quorum
         <6>2. QED
          BY <3>2, <6>1 \** need to first pick BQ in ByzQuorum
            \** and then let Q == BQ \cap Acceptor
        <5>3. ASSUME NEW a \in Q
              PROVE  \E m2av \in acceptorMsgsOfType("2av") :
                       /\ m2av.acc = a
                       /\ m2av.bal = m.bal
                       /\ m2av.val = m.val
          <6>1. PICK m2av \in sentMsgs("2av", b) : /\ m2av.val = v
                                                   /\ m2av.acc = a
            BY <5>2
          <6>2. m2av \in acceptorMsgsOfType("2av")
            BY <6>1 DEF sentMsgs, Quorum  , acceptorMsgsOfType, msgsOfType
          <6> WITNESS m2av \in acceptorMsgsOfType("2av")
          <6> QED
            BY <6>1 DEF sentMsgs
        <5> QED
          BY <5>1, <5>3 DEF 2amsgs
      <4>2. QED
        BY <4>1 DEF P!sentMsgs, msgs
    <3>4. PmaxBal' = [PmaxBal EXCEPT ![self] = b]
      <4>1.  ASSUME NEW a \in Acceptor,
                    a # self
             PROVE  PmaxBal'[a] = PmaxBal[a]
         <5>1. bmsgs' = bmsgs \cup {m2b} /\ m2b.acc = self
           BY <3>2
         <5>2. QED
          BY  <4>1, <5>1, PmaxBalLemma2
      <4>2. PmaxBal'[self] = b
        <5> DEFINE S == {mm.bal : mm \in {ma \in bmsgs :
                                           /\ ma.type \in {"1b", "2b"}
                                           /\ ma.acc = self}}
                   T == S \cup {m2b.bal}
        <5>1. IsFiniteSet(S) /\ (S \in SUBSET Ballot)
          BY PMaxBalLemma3 DEF Inv
        <5>2. IsFiniteSet(T) /\ (T \in SUBSET Ballot)
          BY <5>1, OnePlusFinite
        <5>3. PmaxBal[self] = MaxBallot(S)
          BY DEF PmaxBal, 1bOr2bMsgs
        <5>4. PmaxBal'[self] = MaxBallot(T)
          BY <3>2 DEF PmaxBal, 1bOr2bMsgs
        <5> HIDE DEF S, T
        <5>5. CASE S = {}
          <6>1. T ={b} \cup {}
            BY <5>5 DEF T
          <6>2. /\ b >= b
                /\ b >= -1
            BY SimpleArithmetic DEF Ballot
          <6>3. MaxBallot({b}) = b
            BY <6>2, SingletonSetFinite, MaxBallotLemma1
          <6>4. MaxBallot({}) = -1
            BY EmptySetFinite, MaxBallotProp
          <6> QED
            BY SingletonSetFinite, EmptySetFinite, (*<7>1,*)  <6>1,  <6>2, <6>3, <6>4, MaxBallotLemma2, <5>4
        <5>6. CASE S # {}
          <6>1. \A bb \in S : PmaxBal[self] >= bb
            BY <5>1, <5>3, MaxBallotProp
          <6>2. ASSUME NEW bb \in S
                PROVE  b >= bb
            <7>1. \A pmb \in Ballot \cup {-1} :
                       b >= pmb /\ pmb >= bb => b >= bb
              BY SimpleArithmetic, <5>1 DEF Ballot
            <7>2. QED
              BY <6>1, (*<7>*)<5>1, <7>1,  <3>1, PmaxBalLemma5 DEF Inv
          <6>3. b >= b
            BY SimpleArithmetic DEF Ballot
          <6>4. \A bb \in T : b >= bb
            BY <6>2, <6>3, m2b.bal = b  DEF T
          <6>5. b = MaxBallot(T)
            BY <5>2, <6>4,  MaxBallotLemma1 DEF T
          <6>6. QED
            BY <6>5, <5>4
        <5>7. QED
          BY <5>5, <5>6
      <4>3. QED
        BY <4>1, <4>2 DEF PmaxBal, 1bOr2bMsgs
    <3>5. /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
          /\ maxVVal' = [maxVVal EXCEPT ![self] = m.val]
      BY <3>2 (*, m.val = v *) DEF Phase2b
    <3>6. QED
      <4>1. P!Phase2b(self, b)
        <5>1. P!Phase2b(self, b)!2
          <6> USE <3>3
          <6>1. WITNESS m \in P!sentMsgs("2a", b)
          <6>2. QED
            BY <3>4, <3>5, <3>2
        <5>2. QED
          BY <5>1, <3>1 DEF P!Phase2b
      <4>2. QED
        BY <4>1 DEF P!TLANext, Ballot, P!Ballot
  <2>6. ASSUME NEW self \in Acceptor, NEW b \in Ballot,
               LearnsSent(self, b)
        PROVE  P!TLANext \/ P!vars' = P!vars
    <3> USE LearnsSent(self, b)
    <3>1. PICK SM \in SUBSET {m \in msgsOfType("1c") : m.bal = b} :
                        msgs' = msgs \cup SM
     BY MsgsLemma DEF Inv
    <3> DEFINE S == {m.val : m \in SM}
    <3>2. S \in SUBSET Value
      <4> SUFFICES ASSUME NEW m \in SM
                   PROVE  m.val \in Value
        OBVIOUS
      <4> QED
        BY m \in msgsOfType("1c"), BMessageLemma DEF Inv, TypeOK, msgsOfType, 1cMessage
    <3>3. msgs' = msgs \cup {[type |-> "1c", bal |-> b, val |-> v] : v \in S}
      <4> SUFFICES ASSUME NEW m
                   PROVE m \in SM <=> /\ m = [type |-> "1c", bal |-> b, val |-> m.val]
                                      /\ m.val \in S
        BY <3>1 DEF msgsOfType
      <4>1. ASSUME NEW mm \in SM
            PROVE  /\ mm = [type |-> "1c", bal |-> b, val |-> mm.val]
                   /\ mm.val \in S
        <5>1. /\ mm \in bmsgs
              /\ mm.type = "1c"
              /\ mm.bal = b
          BY <4>1 DEF msgsOfType
        <5>2. mm \in 1cMessage
          BY <5>1, BMessageLemma DEF Inv, TypeOK
        <5>3. mm = [type |-> mm.type, bal |-> mm.bal, val |-> mm.val]
          BY ONLY <5>2 DEF 1cMessage
        <5>4. mm.val \in S
          OBVIOUS
        <5>5. QED
          BY <5>1, <5>3, (* <4>1, *) <5>4 \* DEF 1cMessage
      <4>2. ASSUME /\ m = [type |-> "1c", bal |-> b, val |-> m.val]
                   /\ m.val \in S
            PROVE  m \in SM
        <5>1. PICK mm \in SM : mm.val = m.val
          BY <4>2
        <5>2. mm = [type |-> "1c", bal |-> b, val |-> mm.val]
          BY <4>1
        <5>3. QED
          BY <4>2, <5>1, <5>2
      <4>3. QED
        BY <4>1, <4>2
    <3>4. ASSUME NEW v \in S
          PROVE  \E Q \in Quorum : P!ShowsSafeAt(Q, b, v)
      <4>1. ASSUME NEW ac \in Acceptor,
                   KnowsSafeAt(ac, b, v)'
            PROVE  \E Q \in Quorum : P!ShowsSafeAt(Q, b, v)
        <5>1. bmsgs' = bmsgs
          BY DEF LearnsSent
        <5>  DEFINE Q(BQ) == BQ \cap Acceptor
                    SS == {m \in knowsSent'[ac] : m.bal = b}
                    SQ(BQ) == {1bRestrict(mm) :
                                 mm \in {m \in SS : m.acc \in Q(BQ)}}
                    Q1b(BQ) == {m \in P!sentMsgs("1b", b) : m.acc \in Q(BQ)}
        <5>2. ASSUME NEW BQ \in ByzQuorum,
                     \A a \in BQ : \E m \in SS : m.acc = a
              PROVE  SQ(BQ) = Q1b(BQ)
          <6>1. ASSUME NEW m \in P!sentMsgs("1b", b),
                           m.acc \in Q(BQ)
                       PROVE m \in SQ(BQ)
            <7>1. /\ m \in 1bmsgs
                  /\ m.type = "1b"
                  /\ m.bal = b
              BY MsgsTypeLemma DEF P!sentMsgs, msgs
            <7>2. PICK m1 \in bmsgs : /\ m1.type = "1b"
                                      /\ m1.acc \in Acceptor
                                      /\ m = 1bRestrict(m1)
              BY <7>1 DEF 1bmsgs, acceptorMsgsOfType, msgsOfType
            <7>3. m1.bal = b
              BY <7>1, <7>2 DEF 1bRestrict
            <7>4. PICK m2 \in knowsSent[ac]' :
                         /\ m2.bal = b
                         /\ m2.acc = m.acc
              BY <5>2, <6>1
            <7>5. m2 \in bmsgs /\ m2.type = "1b"
              BY <5>1 DEF InvP, Inv, knowsSentInv, msgsOfType
            <7>6. /\ m1.acc = m.acc
                  /\ m1.bal = b
              BY <7>1, <7>2 DEF 1bRestrict
            <7>7. m1 = m2
              BY  <7>2, <7>4, <7>5, <7>6 DEF Inv, 1bInv2
            <7>8. m2 \in SS /\ m2.acc \in Q(BQ)
              BY <7>7, <6>1, <7>2, <7>4
            <7>9. QED
              BY <7>8, <7>7, <7>2
          <6>2. ASSUME NEW m \in SS,
                       m.acc \in Q(BQ)
                PROVE  1bRestrict(m) \in Q1b(BQ)
            <7>1. /\ m \in bmsgs
                  /\ m.bal = b
                  /\ m.type = "1b"
              BY <5>1 DEF InvP, Inv, knowsSentInv, msgsOfType
            <7>2. m \in acceptorMsgsOfType("1b")
              BY <7>1, <6>2 DEF acceptorMsgsOfType, msgsOfType
            <7>3. 1bRestrict(m) \in msgs
              BY <7>2 DEF msgs, 1bmsgs
            <7>4. QED
              BY <6>2, <7>1, <7>3 DEF P!sentMsgs, 1bRestrict
          <6>3. QED
            BY <6>1, <6>2 DEF Q1b, SQ
        <5>3. CASE KnowsSafeAt(ac, b, v)!1!1'
          <6>1. PICK BQ \in ByzQuorum : KnowsSafeAt(ac, b, v)!1!1!(BQ)'
            BY <5>3
          <6>2. Q(BQ) \in Quorum
            BY DEF Quorum
          <6>3. \A a \in Q(BQ) : \E m \in SS : /\ m.acc = a
                                               /\ m.mbal = -1
            BY <6>1
          <6>4. \A a \in Q(BQ) : \E m \in SQ(BQ) : /\ m.acc = a
                                                   /\ m.mbal = -1
            <7> HIDE DEF SS
            <7> TAKE a \in Q(BQ)
            <7>1. PICK m \in SS : m.acc = a /\ m.mbal = -1
              BY <6>3
            <7>2. 1bRestrict(m) \in SQ(BQ)
              BY <7>1
            <7> WITNESS 1bRestrict(m) \in SQ(BQ)
            <7>3. QED
              BY <7>1 DEF 1bRestrict
          <6>5. \A m \in SQ(BQ) : m.mbal = -1
            <7> TAKE mm \in SQ(BQ)
            <7>1. PICK m \in SS : /\ m \in knowsSent[ac]'
                                  /\ m.bal = b
                                  /\ m.acc \in Q(BQ)
                                  /\ mm = 1bRestrict(m)
              OBVIOUS
            <7>2. PICK mm1 \in SQ(BQ) : /\ mm1.acc = m.acc
                                        /\ mm1.mbal = -1
              BY <7>1, <6>4
            <7>3. PICK m1 \in SS : /\ m1 \in knowsSent[ac]'
                                   /\ m1.bal = b
                                   /\ m1.acc \in Q(BQ)
                                   /\ mm1 = 1bRestrict(m1)
               OBVIOUS
            <7>4. m.acc \in Acceptor
              BY <7>1
            <7>5. /\ m \in bmsgs /\ m1 \in bmsgs
                  /\ m.type = "1b" /\ m1.type = "1b"
              BY <5>1, <7>1, <7>3 DEF InvP, Inv, knowsSentInv, msgsOfType
            <7>6. m.acc = m1.acc
              BY <7>2, <7>3  DEF 1bRestrict
            <7>7. m = m1
              BY <7>5, <7>4, <7>1, <7>3, <7>6   DEF Inv, 1bInv2
            <7>8. m.mbal = -1
              BY <7>7, <7>2, <7>3 DEF 1bRestrict
            <7>9. QED
              BY <7>8, <7>1 DEF 1bRestrict
          <6>6. SQ(BQ) = Q1b(BQ)
            BY  <5>2, <6>1
          <6> HIDE DEF SS, Q, SQ
          <6> WITNESS Q(BQ) \in Quorum
          <6>7. QED
            BY <6>4, <6>5, <6>6 DEF P!ShowsSafeAt
        <5>4. CASE KnowsSafeAt(ac, b, v)!1!2'
          <6>1. PICK c \in 0..(b-1) : KnowsSafeAt(ac, b, v)!1!2!(c)'
            BY <5>4
          <6>2. PICK BQ \in ByzQuorum :
                        \A a \in BQ : \E m \in SS : /\ m.acc = a
                                                    /\ m.mbal =< c
                                                    /\ (m.mbal = c) => (m.mval = v)
            BY <6>1
          <6>3. SQ(BQ) = Q1b(BQ)
            BY <6>2, <5>2
          <6>4. P!ShowsSafeAt(Q(BQ), b, v)!1!1
            <7>1. SUFFICES ASSUME NEW a \in Q(BQ)
                           PROVE \E m \in Q1b(BQ) : m.acc = a
              OBVIOUS
            <7>2. PICK m \in SS : m.acc = a
              BY <6>2
            <7>3. 1bRestrict(m) \in SQ(BQ)
              BY <7>2
            <7>4. 1bRestrict(m).acc = a
              BY <7>2 DEF 1bRestrict
            <7>5. QED
              BY <6>3, <7>3, <7>4
          <6>5. PICK m1c \in msgs :
                  /\ m1c = [type |-> "1c", bal |-> m1c.bal, val |-> v]
                  /\ m1c.bal >= c
                  /\ m1c.bal \in Ballot
             <7>1. PICK WQ \in WeakQuorum :
                  \A a \in WQ : \E m \in SS : /\ m.acc = a
                                              /\ \E r \in m.m2av :
                                                      /\ r.bal >= c
                                                      /\ r.val = v
              BY <6>1
             <7>2. PICK a \in WQ, m \in SS :
                          /\ a \in Acceptor
                          /\ m.acc = a
                          /\ \E r \in m.m2av : /\ r.bal >= c
                                               /\ r.val = v
               <8>1. PICK a \in WQ : a \in Acceptor
                 BY BQA
               <8>2. /\ a \in Acceptor
                     /\ <7>1!(WQ)!(a)
                 BY <7>1, <8>1
               <8>3. QED
                 BY <8>2
             <7>3. /\ m.bal = b
                   /\ m \in bmsgs
                   /\ m.type = "1b"
               BY <5>1 DEF InvP, Inv, knowsSentInv, msgsOfType
             <7>4. PICK r \in m.m2av : /\ r.bal >= c
                                        /\ r.val = v
               BY <7>2
             <7>5. r.bal \in Ballot
               BY <7>2, <7>3, BMessageLemma DEF Inv, TypeOK, 1bMessage \* <8>2
             <7>6. [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
               BY <7>2, <7>3, <7>4 DEF Inv, 1bInv1
             <7>7. QED
               BY <7>2, <7>4, <7>5, <7>6
          <6>6. ASSUME NEW m \in Q1b(BQ)
                PROVE  /\ m1c.bal \geq m.mbal
                       /\ (m1c.bal = m.mbal) => (m.mval = v)
            <7>1. m.acc \in Q(BQ)
              OBVIOUS
            <7>2. PICK mm \in SS : /\ mm.acc = m.acc
                                   /\ mm.mbal =< c
                                   /\ (mm.mbal = c) => (mm.mval = v)
              BY <6>2
            <7>3. PICK mm2 \in SS : /\ mm2.acc = m.acc
                                    /\ m = 1bRestrict(mm2)
              <8>1. PICK mm2 \in SS : m = 1bRestrict(mm2)
                BY <6>3
              <8>2 QED
                BY  <8>1 DEF 1bRestrict
            <7>4. /\ mm = mm2
                  /\ mm2.mbal \in Ballot \cup {-1}
              <8>1. /\ mm \in knowsSent'[ac]
                    /\ mm.bal = b
                    /\ mm2 \in knowsSent'[ac]
                    /\ mm2.bal = b
                OBVIOUS
              <8>2. /\ mm \in bmsgs
                    /\ mm2 \in bmsgs
                    /\ mm.type = "1b"
                    /\ mm2.type = "1b"
                BY <5>1, <8>1 DEF InvP, Inv, knowsSentInv, msgsOfType
              <8>3. mm.acc = mm2.acc
                BY <7>2, <7>3
              <8>4. mm.acc \in Acceptor
                BY <7>1, <7>2
              <8>5. mm2.mbal \in Ballot \cup {-1}
                BY <8>2, BMessageLemma DEF Inv, TypeOK, 1bMessage
              <8>6. QED
                BY <8>1, <8>2, <8>3, <8>4, <8>5 DEF Inv, 1bInv2
            <7>5. /\ m.mbal =< c
                  /\ (m.mbal = c) => (m.mval = v)
                  /\ m.mbal \in Ballot \cup {-1}
              BY <7>2, <7>3, <7>4 DEF 1bRestrict
            <7>6. m1c.bal \geq m.mbal
              <8> \A m1cbal, mmbal \in Ballot \cup {-1} :
                      mmbal =< c /\ m1cbal >= c => m1cbal \geq mmbal
                BY SimpleArithmetic DEF Ballot
              <8> QED
                BY <6>5, <7>5
            <7>7. ASSUME m1c.bal = m.mbal
                  PROVE  m.mval = v
              <8> \A m1cbal, mmbal \in Ballot \cup {-1} :
                   mmbal =< c /\ m1cbal >= c /\ mmbal = m1cbal => mmbal = c
                BY SimpleArithmetic DEF Ballot
              <8> QED
                BY <7>5, <6>5, <7>7
            <7>8. QED
              BY <7>6, <7>7
          <6>7. QED
            <7>1. Q(BQ) \in Quorum
              BY DEF Quorum
            <7>2. P!ShowsSafeAt(Q(BQ), b, v)!1!2!2!(m1c)
              BY <6>5, <6>6
            <7> QED
              BY <7>1, <6>4, <7>2 DEF P!ShowsSafeAt
        <5>5. QED
          BY <4>1, <5>3, <5>4 DEF KnowsSafeAt
      <4>2. \E a \in Acceptor : KnowsSafeAt(a, b, v)'
        <5>1. PICK m \in SM : m.val = v
          OBVIOUS
        <5>2. /\ m \in msgs'
              /\ m.type = "1c"
              /\ m.bal = b
          BY <3>1 DEF msgsOfType
        <5>3. m \in 1cmsgs'
          BY <5>2, MsgsTypeLemmaPrime
        <5> QED
          BY <5>1, <5>2, <5>3 DEF 1cmsgs
      <4>3. QED
        BY <4>1, <4>2
    <3>5. PmaxBal' = PmaxBal
      BY DEF LearnsSent, PmaxBal, 1bOr2bMsgs
    <3>6. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5
         DEF LearnsSent, P!Phase1c, P!TLANext, Ballot, P!Ballot
  <2>7. ASSUME NEW self \in Ballot,
               Phase1a(self)

        PROVE  P!TLANext \/ P!vars' = P!vars
    <3> USE Phase1a(self)
    <3>1. msgs' = msgs \cup {[type |-> "1a", bal |-> self]}
      BY MsgsLemma DEF Inv
    <3>2. UNCHANGED << PmaxBal, maxVBal, maxVVal >>
      BY DEF Phase1a, PmaxBal, 1bOr2bMsgs
    <3>3. P!Phase1a(self)
      BY <3>1, <3>2 DEF P!Phase1a
    <3>4. QED
      BY <3>3 DEF P!TLANext, Ballot, P!Ballot
  <2>8. ASSUME NEW self \in Ballot,
               Phase1c(self)
        PROVE  P!TLANext \/ P!vars' = P!vars
    <3> USE Phase1c(self)
    <3>1. PICK SS \in SUBSET [type : {"1c"}, bal : {self},
                             val : Value] :
                /\ \A m \in SS :
                    \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)
                /\ msgs' = msgs \cup SS
      BY MsgsLemma DEF Inv
    <3> DEFINE S == {m.val : m \in SS}
    <3>2. SS = {[type |-> "1c", bal |-> self,
                  val |-> v] : v \in S}
      <4>1. ASSUME NEW m \in SS
            PROVE  m \in {[type |-> "1c", bal |-> self,
                           val |-> v] : v \in S}
        <5>1. m = [type |-> "1c", bal |-> self, val |-> m.val]
          <6>1. \E a \in {"1c"}, b \in {self}, v \in Value :
                    m =  [type |-> a, bal |-> b, val |-> v]
            OBVIOUS
          <6>2. PICK v \in Value :
                    m =  [type |-> "1c", bal |-> self, val |-> v]
            BY <6>1
          <6>3. [type |-> "1c", bal |-> self, val |-> v].val = v
            OBVIOUS
          <6>4. QED
            BY <6>2, <6>3
        <5>2. m.val \in S
          BY DEF S
        <5>3. QED
          BY <5>1, <5>2
      <4>2. ASSUME NEW m \in {[type |-> "1c", bal |-> self,
                               val |-> v] : v \in S}
            PROVE  m \in SS
        <5>1. PICK v \in S :
                      m = [type |-> "1c", bal |-> self, val |-> v]
         OBVIOUS
        <5>2. PICK mm \in SS : mm.val = v
          OBVIOUS
        <5>3. mm \in [type : {"1c"}, bal : {self}, val : Value]
          OBVIOUS
        <5>4. mm = [type |-> "1c", bal |-> self, val |-> v]
          BY <5>2, <5>3
        <5>5. QED
          BY <5>1, <5>4
      <4>3. QED
        BY <4>1, <4>2
    <3>3. ASSUME NEW v \in S
          PROVE  \E Q \in Quorum : P!ShowsSafeAt(Q, self, v)
      <4> DEFINE m == [type |-> "1c", bal |-> self, val |-> v]
      <4>1. m \in SS
        BY <3>2
      <4>2. PICK a \in Acceptor : KnowsSafeAt(a, self, v)
        BY <4>1, <3>1
      <4> DEFINE SK == {mm \in knowsSent[a] : mm.bal = self}
      <4>3. ASSUME NEW BQ \in ByzQuorum,
                       \A ac \in BQ : \E mm \in SK : mm.acc = ac
             PROVE  P!ShowsSafeAt(BQ \cap Acceptor, self, v)!1!1
        <5> DEFINE Q == BQ \cap Acceptor
                   Q1b == {mm \in P!sentMsgs("1b", self) : mm.acc \in Q}
        <5> SUFFICES ASSUME NEW ac \in BQ \cap Acceptor
                     PROVE  \E mm \in Q1b : mm.acc = ac
          OBVIOUS
        <5>1. \A mm \in acceptorMsgsOfType("1b") :
                 (mm.bal = self) =>
                    (1bRestrict(mm) \in P!sentMsgs("1b", self))
          <6> SUFFICES ASSUME NEW mm \in acceptorMsgsOfType("1b"),
                                  mm.bal = self
                       PROVE 1bRestrict(mm) \in P!sentMsgs("1b", self)
            OBVIOUS
          <6>1. /\ 1bRestrict(mm).type = "1b"
                /\ 1bRestrict(mm).bal = self
            BY DEF 1bRestrict, acceptorMsgsOfType, msgsOfType
          <6>2. 1bRestrict(mm) \in msgs
            BY DEF 1bmsgs, msgs
          <6>3. QED
            BY <6>1, <6>2 DEF P!sentMsgs
        <5>2. PICK mm \in SK : mm.acc = ac
          BY <4>3
        <5>3. mm \in msgsOfType("1b") /\ mm.bal = self
          BY DEF Inv, knowsSentInv
        <5>4. 1bRestrict(mm) \in P!sentMsgs("1b", self)
          BY <5>1, <5>2, <5>3 DEF acceptorMsgsOfType
        <5>5. 1bRestrict(mm).acc = ac
          BY <5>2 DEF 1bRestrict
        <5>6. QED
          BY <5>4, <5>5
      <4>4. CASE KnowsSafeAt(a, self, v)!1!1
        <5>1. PICK BQ \in ByzQuorum :
                     \A ac \in BQ : \E mm \in SK : /\ mm.acc = ac
                                                   /\ mm.mbal = -1
          BY <4>4
        <5> DEFINE Q == BQ \cap Acceptor
                   Q1b == {mm \in P!sentMsgs("1b", self) : mm.acc \in Q}
        <5>2. P!ShowsSafeAt(Q, self, v)!1!1
          <6>1. \A ac \in BQ : \E mm \in SK :  mm.acc = ac
            BY <5>1
          <6>2. QED
            BY <6>1, <4>3
        <5>3. ASSUME NEW mm \in Q1b
              PROVE  mm.mbal = -1
          <6>1. /\ mm \in 1bmsgs
                /\ mm.bal = self
                /\ mm.acc \in Q
            BY MsgsTypeLemma DEF P!sentMsgs
          <6>2. PICK mb \in bmsgs : /\ mb.type = "1b"
                                    /\ mm = 1bRestrict(mb)
            BY <6>1 DEF 1bmsgs, acceptorMsgsOfType, msgsOfType
          <6>3. /\ mb.bal = self
                /\ mb.acc \in Q
            BY <6>1, <6>2 DEF 1bRestrict
          <6>4. PICK mk \in SK : (mk.acc = mb.acc) /\ (mk.mbal = -1)
            BY <6>3, <5>1
          <6>5. (mk \in bmsgs) /\ (mk.bal = self) /\ (mk.type = "1b")
            BY DEF Inv, knowsSentInv, msgsOfType
          <6>6. mk = mb
            BY <6>2, <6>3, <6>4, <6>5 DEF Inv, 1bInv2
          <6>7. QED
            BY <6>6, <6>4, <6>2 DEF 1bRestrict
        <5>4. QED
          <6> USE DEF Quorum
          <6> WITNESS Q \in Quorum
          <6> QED
            BY <5>2, <5>3 DEF P!ShowsSafeAt, Quorum
      <4>5. CASE KnowsSafeAt(a, self, v)!1!2
        <5>1. PICK c \in 0..(self-1) : KnowsSafeAt(a, self, v)!1!2!(c)
          BY <4>5
        <5>2. PICK BQ \in ByzQuorum : KnowsSafeAt(a, self, v)!1!2!(c)!1!(BQ)
          BY <5>1
        <5> DEFINE Q == BQ \cap Acceptor
                   Q1b == {mm \in P!sentMsgs("1b", self) : mm.acc \in Q}
        <5>3. P!ShowsSafeAt(Q, self, v)!1!1
          <6>1. \A ac \in BQ : \E mm \in SK : mm.acc = ac
            BY <5>2
          <6>2. QED
            BY <6>1, <4>3
        <5>4. PICK WQ \in WeakQuorum : KnowsSafeAt(a, self, v)!1!2!(c)!2!(WQ)
          BY <5>1
        <5>5. PICK ac \in WQ \cap Acceptor :
                KnowsSafeAt(a, self, v)!1!2!(c)!2!(WQ)!(ac)
          <6>1. \E ac \in WQ \cap Acceptor : TRUE
            BY BQA
          <6>2. QED
          BY <6>1, <5>4
        <5>6. PICK mk \in SK : /\ mk.acc = ac
                               /\ \E r \in mk.m2av : /\ r.bal >= c
                                                     /\ r.val = v
          BY <5>5
        <5>7. PICK r \in mk.m2av : /\ r.bal >= c
                                    /\ r.val = v
          BY <5>6
        <5>8. (mk \in bmsgs) /\ (mk.type = "1b") /\ (mk.bal = self)
          BY DEF Inv, knowsSentInv, msgsOfType
        <5> DEFINE mc == [type |-> "1c", bal |-> r.bal, val |-> v]
        <5>9. mc \in msgs
          <6>1. [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs
            BY <5>6, <5>8 DEF Inv, 1bInv1
          <6>2. QED
            BY <6>1, <5>7
        <5>10. ASSUME NEW mq \in  Q1b
               PROVE  /\ mc.bal \geq mq.mbal
                      /\(mc.bal = mq.mbal) => (mq.mval = v)
          <6>1. /\ mq \in msgs
                /\ mq.type = "1b"
                /\ mq.bal = self
                /\ mq.acc \in Q
            BY DEF P!sentMsgs
          <6>2.PICK mbq \in acceptorMsgsOfType("1b") :
                       mq = 1bRestrict(mbq)
            BY <6>1, MsgsTypeLemma DEF 1bmsgs
          <6>3. /\ mbq \in bmsgs
                /\ mbq.type = "1b"
                /\ mbq.bal = self
                /\ mbq.mbal = mq.mbal
                /\ mbq.mval = mq.mval
                /\ mbq.acc \in Q
            BY <6>1, <6>2 DEF acceptorMsgsOfType, msgsOfType, 1bRestrict
          <6>4. PICK ab \in BQ :
                       \E mcq \in SK : /\ mcq.acc = mbq.acc
                                       /\ mcq.mbal =< c
                                       /\ (mcq.mbal = c) => (mcq.mval = v)
            BY <5>2, <6>3
          <6>5. PICK mcq : /\ mcq \in knowsSent[a]
                           /\ mcq.bal = self
                           /\ mcq.acc = mbq.acc
                           /\ mcq.mbal =< c
                           /\ (mcq.mbal = c) => (mcq.mval = v)
            BY <6>4
          <6>6. (mcq \in bmsgs) /\ (mcq.type = "1b")
            BY <6>5 DEF Inv, knowsSentInv, msgsOfType
          <6>7. mcq = mbq
            BY <6>3, <6>5, <6>6 DEF Inv, 1bInv2
          <6>8.  /\ mc.bal \geq mcq.mbal
                 /\ (mc.bal = mcq.mbal) => (mcq.mval = v)
            <7>1. mc.bal \in Ballot \cup {-1} /\ mc.bal >= c
              <8>1. mc.bal = r.bal
                OBVIOUS
              <8>2. mk \in bmsgs /\ mk.type = "1b"
                BY DEF Inv, knowsSentInv, msgsOfType
              <8>3. r.bal \in Ballot
                <9>1. mk \in 1bMessage
                  BY <8>2, BMessageLemma DEF Inv, TypeOK \* , 1bMessage
                <9>2. QED
                  BY <9>1 DEF 1bMessage
              <8>4. QED
                BY <8>1, <8>3, <5>7
            <7>2. mcq.mbal \in Ballot \cup {-1}
              <8> mcq \in bmsgs /\ mcq.type = "1b"
                BY <6>5 DEF Inv, knowsSentInv, msgsOfType
              <8> QED
                BY BMessageLemma DEF Inv, TypeOK, 1bMessage
            <7>3. \A mcbal, mcqmbal \in Ballot \cup {-1} :
                       /\ mcbal >= c
                       /\ mcqmbal =< c
                       => /\ mcbal \geq mcqmbal
                          /\ (mcbal = mcqmbal) => (mcqmbal = c)
              BY SimpleArithmetic DEF Ballot
            <7>4. /\ mc.bal \geq mcq.mbal
                  /\ (mc.bal = mcq.mbal) => (mcq.mbal = c)
              BY <7>1, <7>2, <7>3, <6>5
            <7>5. QED
              BY <7>4, <6>5
          <6>9. QED
            BY  <6>3, <6>7, <6>8
        <5>11. QED
          <6> Q \in Quorum
            BY DEF Quorum
          <6> WITNESS Q \in Quorum
          <6> QED
            BY <5>3, <5>9, <5>10 DEF P!ShowsSafeAt
      <4>6. QED
        BY <4>2, <4>4, <4>5 DEF KnowsSafeAt
    <3>4. P!Phase1c(self, S)
      BY <3>1, <3>2, <3>3 DEF P!Phase1c, Phase1c, PmaxBal, 1bOr2bMsgs
    <3>5. QED
      BY <3>4 DEF P!TLANext, Ballot, P!Ballot
  <2>9. ASSUME NEW self \in FakeAcceptor,
               FakingAcceptor(self)
        PROVE  P!TLANext \/ P!vars' = P!vars
    <3> USE FakingAcceptor(self)
    <3>1. msgs' = msgs
      BY MsgsLemma DEF Inv
    <3>2. PmaxBal' = PmaxBal
      <4>1. PICK mm : /\ bmsgs' = bmsgs \cup {mm}
                      /\ mm.acc = self
        BY DEF FakingAcceptor
      <4> DEFINE S(b, a) == {ma \in b : /\ ma.type \in {"1b", "2b"}
                                        /\ ma.acc = a}
      <4>2. ASSUME NEW a \in Acceptor
            PROVE  S(bmsgs, a) = S(bmsgs', a)
        <5>1. \A m : (m.acc = a) => (m \in bmsgs' <=> m \in bmsgs)
          BY <4>1, BQA
        <5>2. QED
          BY <5>1
      <4> QED
        BY <4>2 DEF PmaxBal, 1bOr2bMsgs
    <3>3. P!vars' = P!vars
      BY <3>1, <3>2 DEF P!vars, FakingAcceptor
    <3>4. QED
      BY <3>3
  <2>10. QED
    BY  <2>3,  <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, NextDef

<1>3. QED
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(* To see how learning is implemented, we must describe how to determine   *)
(* that a value has been chosen.  This is done by the following definition *)
(* of `chosen' to be the set of chosen values.                             *)
(***************************************************************************)
chosen == {v \in Value : \E BQ \in ByzQuorum, b \in Ballot :
                           \A a \in BQ : \E m \in msgs : /\ m.type = "2b"
                                                         /\ m.acc  = a
                                                         /\ m.bal  = b
                                                         /\ m.val  = v}
(***************************************************************************)
(* The correctness of our definition of `chosen' is expressed by the       *)
(* following theorem, which asserts that if a value is in `chosen', then   *)
(* it is also in the set `chosen' of the emulated execution of the         *)
(* PCon algorithm.                                                         *)
(*                                                                         *)
(* The state function `chosen' does not necessarily equal the              *)
(* corresponding state function of the PCon algorithm.  It                 *)
(* requires every (real or fake) acceptor in a ByzQuorum to vote for (send *)
(* 2b messages) for a value v in the same ballot for v to be in `chosen'   *)
(* for the BPCon algorithm, but it requires only that every (real)         *)
(* acceptor in a Quorum vote for v in the same ballot for v to be in the   *)
(* set `chosen' of the emulated execution of algorithm PCon.               *)
(*                                                                         *)
(* Liveness for BPCon requires that, under suitable assumptions, some      *)
(* value is eventually in `chosen'.  Since we can't assume that a fake     *)
(* acceptor does anything useful, liveness requires the assumption that    *)
(* there is a ByzQuorum composed entirely of real acceptors (the second    *)
(* conjunct of assumption BQLA.                                            *)
(***************************************************************************)
THEOREM chosen \subseteq P!chosen
\* Note: I had to define ch and Pch instead of using subexpression
\* names because of a bug in tlapm that has since been fixed.
<1> DEFINE ch(v) == \E BQ \in ByzQuorum, b \in Ballot :
                           \A a \in BQ : \E m \in msgs : /\ m.type = "2b"
                                                         /\ m.acc  = a
                                                         /\ m.bal  = b
                                                         /\ m.val  = v
           Pch(v) == \E Q \in Quorum, b \in P!Ballot :
                           \A a \in Q : \E m \in msgs : /\ m.type = "2b"
                                                        /\ m.acc  = a
                                                        /\ m.bal  = b
                                                        /\ m.val  = v
<1> SUFFICES ASSUME NEW v \in Value, ch(v)
             PROVE  Pch(v)
  BY DEF chosen, P!chosen

<1>1. PICK BQ \in ByzQuorum, b \in Ballot : ch(v)!(BQ, b)
  OBVIOUS
<1> DEFINE Q == BQ \cap Acceptor
<1>2. Q \in Quorum
  BY DEF Quorum
<1> WITNESS Q \in Quorum
<1> USE DEF P!Ballot, Ballot
<1> WITNESS b \in P!Ballot
<1>3. QED
  BY <1>1
==============================================================================
\* Modification History
\* Last modified Wed Apr 15 15:16:26 CEST 2020 by doligez
\* Last modified Mon Aug 18 14:57:27 CEST 2014 by tomer
\* Last modified Mon Mar 04 17:24:05 CET 2013 by doligez
\* Last modified Wed Nov 30 15:47:26 PST 2011 by lamport
\* Last modified Wed Dec 01 11:35:29 PST 2010 by lamport
