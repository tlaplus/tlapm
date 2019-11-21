----------------------------- MODULE VoteProof ------------------------------ 
(***************************************************************************)
(* This is a high-level consensus algorithm in which a set of processes    *)
(* called `acceptors' cooperatively choose a value.  The algorithm uses    *)
(* numbered ballots, where a ballot is a round of voting.  Acceptors cast  *)
(* votes in ballots, casting at most one vote per ballot.  A value is      *)
(* chosen when a large enough set of acceptors, called a `quorum', have    *)
(* all voted for the same value in the same ballot.                        *)
(*                                                                         *)
(* Ballots are not executed in order.  Different acceptors may be          *)
(* concurrently performing actions for different ballots.                  *)
(***************************************************************************)
EXTENDS Integers , FiniteSets, TLC, TLAPS

\* THEOREM SMT == TRUE (*{ by (smt) }*)
-----------------------------------------------------------------------------
CONSTANT Value,     \* As in module Consensus, the set of choosable values.
         Acceptor,  \* The set of all acceptors.
         Quorum     \* The set of all quorums.
 
(***************************************************************************)
(* The following assumption asserts that a quorum is a set of acceptors,   *)
(* and the fundamental assumption we make about quorums: any two quorums   *)
(* have a non-empty intersection.                                          *)
(***************************************************************************)
ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}  
 
THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
PROOF BY QA
-----------------------------------------------------------------------------
(***************************************************************************)
(* Ballot is the set of all ballot numbers.  For simplicity, we let it be  *)
(* the set of natural numbers.  However, we write Ballot for that set to   *)
(* make it clear what the function of those natural numbers are.           *)
(*                                                                         *)
(* The algorithm and its refinements work with Ballot any set with minimal *)
(* element 0, -1 not an element of Ballot, and a well-founded total order  *)
(* < on Ballot \cup {-1} with minimal element -1, and 0 < b for all        *)
(* non-zero b in Ballot.  In the proof, any set of the form i..j must be   *)
(* replaced by the set of all elements b in Ballot \cup {-1} with i \leq b *)
(* \leq j, and i..(j-1) by the set of such b with i \leq b < j.            *)
(***************************************************************************)
Ballot == Nat
-----------------------------------------------------------------------------
(***************************************************************************)
(* In the algorithm, each acceptor can cast one or more votes, where each  *)
(* vote cast by an acceptor has the form <<b, v>> indicating that the      *)
(* acceptor has voted for value v in ballot b.  A value is chosen if a     *)
(* quorum of acceptors have voted for it in the same ballot.               *)
(*                                                                         *)
(* The algorithm uses two variables, `votes' and `maxBal', both arrays     *)
(* indexed by acceptor.  Their meanings are:                               *)
(*                                                                         *)
(*   votes[a] - The set of votes cast by acceptor `a'.                     *)
(*                                                                         *)
(*   maxBal[a] - The number of the highest-numbered ballot in which `a'    *)
(*               has cast a vote, or -1 if it has not yet voted.           *)
(*                                                                         *)
(* The algorithm does not let acceptor `a' vote in any ballot less than    *)
(* maxBal[a].                                                              *)
(*                                                                         *)
(* We specify our algorithm by the following PlusCal algorithm.  The       *)
(* specification Spec defined by this algorithm describes only the safety  *)
(* properties of the algorithm.  In other words, it specifies what steps   *)
(* the algorithm may take.  It does not require that any (non-stuttering)  *)
(* steps be taken.  We prove that this specification Spec implements the   *)
(* specification Spec of module Consensus under a refinement mapping       *)
(* defined below.  This shows that the safety properties of the voting     *)
(* algorithm (and hence the algorithm with additional liveness             *)
(* requirements) imply the safety properties of the Consensus              *)
(* specification.  Liveness is discussed later.                            *)
(***************************************************************************)
 
(***************************
--algorithm Voting {
  variables votes = [a \in Acceptor |-> {}],
            maxBal = [a \in Acceptor |-> -1];
  define {
   (************************************************************************)
   (* We now define the operator SafeAt so SafeAt(b, v) is function of the *)
   (* state that equals TRUE if no value other than v has been chosen or   *)
   (* can ever be chosen in the future (because the values of the          *)
   (* variables votes and maxBal are such that the algorithm does not      *)
   (* allow enough acceptors to vote for it).  We say that value v is safe *)
   (* at ballot number b iff Safe(b, v) is true.  We define Safe in terms  *)
   (* of the following two operators.                                      *)
   (*                                                                      *)
   (* Note: This definition is weaker than would be necessary to allow a   *)
   (* refinement of ordinary Paxos consensus, since it allows different    *)
   (* quorums to "cooperate" in determining safety at b.  This is used in  *)
   (* algorithms like Vertical Paxos that are designed to allow            *)
   (* reconfiguration within a single consensus instance, but not in       *)
   (* ordinary Paxos.  See                                                 *)
   (*                                                                      *)
   (*    AUTHOR    = "Leslie Lamport and Dahlia Malkhi and Lidong Zhou ",  *)
   (*    TITLE     = "Vertical Paxos and Primary-Backup Replication",      *)
   (*    Journal   = "ACM SIGACT News (Distributed Computing Column)",     *)
   (*    editor    = {Srikanta Tirthapura and Lorenzo Alvisi},             *)
   (*    booktitle = {PODC},                                               *)
   (*    publisher = {ACM},                                                *)
   (*    YEAR = 2009,                                                      *)
   (*    PAGES = "312--313"                                                *)
   (************************************************************************)
   VotedFor(a, b, v) == <<b, v>> \in votes[a]
     (**********************************************************************)
     (* True iff acceptor a has voted for v in ballot b.                   *)
     (**********************************************************************)
   DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v) 

   (************************************************************************)
   (* We now define SafeAt.  We define it recursively.  The nicest         *)
   (* definition is                                                        *)
   (*                                                                      *)
   (*    RECURSIVE SafeAt(_, _)                                            *)
   (*    SafeAt(b, v) ==                                                   *)
   (*      \/ b = 0                                                        *)
   (*      \/ \E Q \in Quorum :                                            *)
   (*           /\ \A a \in Q : maxBal[a] \geq b                           *)
   (*           /\ \E c \in -1..(b-1) :                                    *)
   (*                /\ (c # -1) => /\ SafeAt(c, v)                        *)
   (*                               /\ \A a \in Q :                        *)
   (*                                    \A w \in Value :                  *)
   (*                                        VotedFor(a, c, w) => (w = v)  *)
   (*          /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)      *)
   (*                                                                      *)
   (* However, TLAPS does not currently support recursive operator         *)
   (* definitions.  We therefore define it as follows using a recursive    *)
   (* function definition.                                                 *)
   (************************************************************************)
   SafeAt(b, v) ==
     LET SA[bb \in Ballot] ==
           (****************************************************************)
           (* This recursively defines SA[bb] to equal SafeAt(bb, v).      *)
           (****************************************************************)
           \/ bb = 0
           \/ \E Q \in Quorum :
                /\ \A a \in Q : maxBal[a] \geq bb
                /\ \E c \in -1..(bb-1) :
                     /\ (c # -1) => /\ SA[c]
                                    /\ \A a \in Q :
                                         \A w \in Value :
                                            VotedFor(a, c, w) => (w = v)
                     /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
     IN  SA[b]
    }
  (*************************************************************************)
  (* There are two possible actions that an acceptor can perform, each     *)
  (* defined by a macro.  In these macros, `self' is the acceptor that is  *)
  (* to perform the action.  The first action, IncreaseMaxBal(b) allows    *)
  (* acceptor `self' to set maxBal[self] to b if b is greater than the     *)
  (* current value of maxBal[self].                                        *)
  (*************************************************************************)
  macro IncreaseMaxBal(b) {
    when b > maxBal[self] ;
    maxBal[self] := b
    }
    
  (*************************************************************************)
  (* Action VoteFor(b, v) allows acceptor `self' to vote for value v in    *)
  (* ballot b if its `when' condition is satisfied.                        *)
  (*************************************************************************)
  macro VoteFor(b, v) {
    when /\ maxBal[self] \leq b
         /\ DidNotVoteIn(self, b)
         /\ \A p \in Acceptor \ {self} : 
               \A w \in Value : VotedFor(p, b, w) => (w = v)
         /\ SafeAt(b, v) ;
    votes[self]  := votes[self] \cup {<<b, v>>};
    maxBal[self] := b 
    }
    
  (*************************************************************************)
  (* The following process declaration asserts that every process `self'   *)
  (* in the set Acceptor executes its body, which loops forever            *)
  (* nondeterministically choosing a Ballot b and executing either an      *)
  (* IncreaseMaxBal(b) action or nondeterministically choosing a value v   *)
  (* and executing a VoteFor(b, v) action.  The single label indicates     *)
  (* that an entire execution of the body of the `while' loop is performed *)
  (* as a single atomic action.                                            *)
  (*                                                                       *)
  (* From this intuitive description of the process declaration, one might *)
  (* think that a process could be deadlocked by choosing a ballot b in    *)
  (* which neither an IncreaseMaxBal(b) action nor any VoteFor(b, v)       *)
  (* action is enabled.  An examination of the TLA+ translation (and an    *)
  (* elementary knowledge of the meaning of existential quantification)    *)
  (* shows that this is not the case.  You can think of all possible       *)
  (* choices of b and of v being examined simultaneously, and one of the   *)
  (* choices for which a step is possible being made.                      *)
  (*************************************************************************)
  process (acceptor \in Acceptor) {
    acc : while (TRUE) {
           with (b \in Ballot) {
             either IncreaseMaxBal(b)
             or     with (v \in Value) { VoteFor(b, v) }
       }
     }
    }
}

The following is the TLA+ specification produced by the translation.
Blank lines, produced by the translation because of the comments, have
been deleted.
****************************)
\* BEGIN TRANSLATION
VARIABLES votes, maxBal

(* define statement *)
VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

SafeAt(b, v) ==
  LET SA[bb \in Ballot] ==
        \/ bb = 0
        \/ \E Q \in Quorum :
             /\ \A a \in Q : maxBal[a] \geq bb
             /\ \E c \in -1..(bb-1) :
                  /\ (c # -1) => /\ SA[c]
                                 /\ \A a \in Q :
                                      \A w \in Value :
                                         VotedFor(a, c, w) => (w = v)
                  /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
  IN  SA[b]

vars == << votes, maxBal >>

ProcSet == (Acceptor)

Init == (* Global variables *)
        /\ votes = [a \in Acceptor |-> {}]
        /\ maxBal = [a \in Acceptor |-> -1]

acceptor(self) == \E b \in Ballot:
                    \/ /\ b > maxBal[self]
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ UNCHANGED votes
                    \/ /\ \E v \in Value:
                            /\ /\ maxBal[self] \leq b
                               /\ DidNotVoteIn(self, b)
                               /\ \A p \in Acceptor \ {self} :
                                     \A w \in Value : VotedFor(p, b, w) => (w = v)
                               /\ SafeAt(b, v)
                            /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
                            /\ maxBal' = [maxBal EXCEPT ![self] = b]


Next == (\E self \in Acceptor: acceptor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* To reason about a recursively-defined operator, one must prove a        *)
(* theorem about it.  In particular, to reason about SafeAt, we need to    *)
(* prove that SafeAt(b, v) equals the right-hand side of its definition,   *)
(* for b \in Ballot and v \in Value.  This is not automatically true for a *)
(* recursive definition.  For example, from the recursive definition       *)
(*                                                                         *)
(*   Silly[n \in Nat] == CHOOSE v : v # Silly[n]                           *)
(*                                                                         *)
(* we cannot deduce that                                                   *)
(*                                                                         *)
(*   Silly[42] = CHOOSE v : v # Silly[42]                                  *)
(*                                                                         *)
(* (From that, we could easily deduce Silly[42] # Silly[42].)              *)
(*                                                                         *)
(* To prove the desired property of SafeAt, we use the following proof     *)
(* rule.  It will eventually be in a standard module--probably in TLAPS.   *)
(* However, for now, we put it here.                                       *)
(***************************************************************************)

THEOREM RecursiveFcnOfNat ==
          ASSUME NEW Def(_,_), 
                 \A n \in Nat : 
                    \A g, h : (\A i \in 0..(n-1) : g[i] = h[i]) => (Def(g, n) = Def(h, n))
          PROVE  LET f[n \in Nat] == Def(f, n)
                 IN  f = [n \in Nat |-> Def(f, n)]
PROOF OMITTED

(***************************************************************************)
(* Here is the theorem that essentially asserts that SafeAt(b, v) equals   *)
(* the right-hand side of its definition.                                  *)
(***************************************************************************)
THEOREM SafeAtProp ==
  \A b \in Ballot, v \in Value :
    SafeAt(b, v) =
      \/ b = 0
      \/ \E Q \in Quorum :
           /\ \A a \in Q : maxBal[a] \geq b
           /\ \E c \in -1..(b-1) :
                /\ (c # -1) => /\ SafeAt(c, v)
                               /\ \A a \in Q :
                                    \A w \in Value :
                                        VotedFor(a, c, w) => (w = v)
                /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
<1>1. SUFFICES ASSUME NEW v \in Value
               PROVE  \A b \in Ballot : SafeAtProp!(b, v)
  OBVIOUS
<1> USE DEF Ballot
<1> DEFINE Def(SA, bb) ==
        \/ bb = 0
        \/ \E Q \in Quorum :
             /\ \A a \in Q : maxBal[a] \geq bb
             /\ \E c \in -1..(bb-1) :
                  /\ (c # -1) => /\ SA[c]
                                 /\ \A a \in Q :
                                      \A w \in Value :
                                         VotedFor(a, c, w) => (w = v)
                  /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
      SA[bb \in Ballot] == Def(SA, bb)
<1>2. \A b : SafeAt(b, v) = SA[b]
  BY DEF SafeAt
<1>3. \A n \in Nat : 
         \A g, h : (\A i \in 0..(n-1) : g[i] = h[i]) => (Def(g, n) = Def(h, n))
  <2>1. SUFFICES ASSUME NEW n \in Nat, NEW g, NEW h,
                        \A i \in 0..(n-1) : g[i] = h[i]
                 PROVE  Def(g, n) = Def(h, n)
    OBVIOUS
  <2>2. Def(g, n)!2 = Def(h, n)!2  
   <3>1.  ASSUME NEW Q \in Quorum,
                 NEW c \in -1..(n-1),
                 c # -1
          PROVE  Def(g, n)!2!(Q)!2!(c)!1!2 = Def(h, n)!2!(Q)!2!(c)!1!2

     <4>1. SUFFICES g[c] = h[c]
       OBVIOUS
     <4>2. c \in 0..(n-1)
       BY <3>1, SimpleArithmetic
     <4>3. QED
       BY <4>2, <2>1 
   <3>2. QED
     BY <3>1
  <2>3. QED
    BY <2>1, <2>2
<1>4. SA = [b \in Ballot |-> Def(SA, b)]
  <2> HIDE DEF Def
  <2> QED
    BY ONLY <1>3, RecursiveFcnOfNat    
<1>5. \A b \in Ballot : SA[b] = Def(SA, b)
  <2> HIDE DEF Def
  <2> QED
    BY <1>4
<1>6. QED
  BY <1>2, <1>5 DEF SafeAt
-----------------------------------------------------------------------------

(***************************************************************************)
(* We now define TypeOK to be the type-correctness invariant.              *)
(***************************************************************************)
TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

(***************************************************************************)
(* We now define `chosen' to be the state function so that the algorithm   *)
(* specified by formula Spec conjoined with the liveness requirements      *)
(* described below implements the algorithm of module Consensus (satisfies *)
(* the specification LiveSpec of that module) under a refinement mapping   *)
(* that substitutes this state function `chosen' for the variable `chosen' *)
(* of module Consensus.  The definition uses the following one, which      *)
(* defines ChosenIn(b, v) to be true iff a quorum of acceptors have all    *)
(* voted for v in ballot b.                                                *)
(***************************************************************************)
ChosenIn(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenIn(b, v)}
-----------------------------------------------------------------------------
(***************************************************************************)
(*                         Mathematical Induction                          *)
(*                                                                         *)
(* The following axiom asserts the validity of a standard proof by         *)
(* mathematical induction.  Some such axiom should be included in the      *)
(* standard TLAPS module.  However, instead of a rule expressed it in      *)
(* terms of a function f, it would be more convenient to use one expressed *)
(* as follows in terms of an operator f:                                   *)
(*                                                                         *)
(*    AXIOM ASSUME NEW f(_), f(0), \A n \in Nat : f(n) => f(n+1)           *)
(*          PROVE  \A n \in Nat : f(n)                                     *)
(*                                                                         *)
(* However, the TLAPS proof system cannot yet handle proofs that use this  *)
(* rule.  So, for now we use this axiom.                                   *)
(***************************************************************************)
AXIOM SimpleNatInduction == \A f : /\ f[0]
                                   /\ \A n \in Nat : f[n] => f[n+1]
                                   => \A n \in Nat : f[n]

(***************************************************************************)
(* We use the SimpleNatInduction rule to prove the following rule, which   *)
(* expresses the soundness of what I believe is sometimes called "General  *)
(* Induction" or "Strong Induction".                                       *)
(***************************************************************************)                                
THEOREM GeneralNatInduction == 
         \A f : /\ f[0]
                /\ \A n \in Nat : (\A j \in 0..n : f[j]) => f[n+1]
                => \A n \in Nat : f[n]
<1>1. SUFFICES ASSUME NEW f,
                      f[0],
                      \A m \in Nat : (\A j \in 0..m : f[j]) => f[m+1],
                      NEW n \in Nat
               PROVE  f[n]
  OBVIOUS
<1> DEFINE g == [m \in Nat |-> \A j \in 0..m : f[j]]
<1>2. g[0]
  <2>1. \A x \in 0..0 : x = 0
    BY SimpleArithmetic
  <2> QED
    BY <1>1, <2>1
<1>3. ASSUME NEW k \in Nat,  g[k]
      PROVE  g[k+1]
  <2>1. /\ k \in 0..k
        /\ k+1 \in Nat
        /\ \A x \in 0..(k+1) : (x \in 0..k) \/ (x = k+1)
    BY SimpleArithmetic
  <2>2. \A j \in 0..k : f[j]
    BY <1>3, <2>1
  <2>3. f[k+1]
    BY <1>1, <2>1, <2>2
  <2>4. QED
    BY <2>1, <2>2, <2>3
<1>4. \A k \in Nat : g[k]
  BY <1>2, <1>3, SimpleNatInduction
<1>5. QED  
  <2>1. n \in 0..n
    BY SimpleArithmetic
  <2>2. QED
    BY <2>1, <1>4                            
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma is used for reasoning about the operator SafeAt.    *)
(* It is proved from SafeAtProp by GeneralNatInduction.                    *)
(***************************************************************************)
LEMMA SafeLemma == 
       TypeOK => 
         \A b \in Ballot :
           \A v \in Value :
              SafeAt(b, v) => 
                \A c \in 0..(b-1) :
                  \E Q \in Quorum :
                    \A a \in Q : /\ maxBal[a] >= c
                                 /\ \/ DidNotVoteIn(a, c)
                                    \/ VotedFor(a, c, v)
<1> SUFFICES ASSUME TypeOK
             PROVE  SafeLemma!2
  OBVIOUS
<1> DEFINE P[b \in Ballot] == \A c \in 0..b : SafeLemma!2!(c)
<1>1. P[0]
  <2>1. SUFFICES ASSUME NEW c \in 0..0
                 PROVE  SafeLemma!2!(c)
    BY DEF Ballot
  <2>2. c = 0 
    BY SimpleArithmetic DEF Ballot
  <2>3. 0..(0-1) = {}
    <3>1. \A x \in 0..(0-1) : FALSE
      BY SimpleArithmetic
    <3>2. QED
      BY <3>1 
  <2>4. QED
    BY <2>2, <2>3
<1>2. ASSUME NEW b \in Ballot, P[b]
      PROVE  P[b+1]
  <2>1. /\ b+1 \in Ballot 
        /\ (b+1) - 1 = b
    BY SimpleArithmetic DEF Ballot
  <2>2. 0..(b+1) = (0..b) \cup {b+1}
    <3>1. \A x \in 0..(b+1) : x \in 0..b \/ x = b+1
      BY SimpleArithmetic DEF Ballot
    <3>2. b+1 \in 0..(b+1) /\ \A x \in 0..b : x \in 0..(b+1)
      BY SimpleArithmetic DEF Ballot
    <3>3. QED
      BY <3>1, <3>2
  <2>3. SUFFICES ASSUME NEW v \in Value,
                        SafeAt(b+1, v),
                        NEW c \in 0..b
                 PROVE  \E Q \in Quorum :
                           \A a \in Q : /\ maxBal[a] >= c
                                        /\ \/ DidNotVoteIn(a, c)
                                           \/ VotedFor(a, c, v)
    BY <1>2, <2>1, <2>2  
  <2>4. PICK Q \in Quorum : 
               /\ \A a \in Q : maxBal[a] \geq (b+1)
               /\ \E cc \in -1..b :
                    /\ (cc # -1) => /\ SafeAt(cc, v)
                                    /\ \A a \in Q :
                                         \A w \in Value :
                                            VotedFor(a, cc, w) => (w = v)
                    /\ \A d \in (cc+1)..b, a \in Q : DidNotVoteIn(a, d)
    <3>1. b+1 # 0
      BY SimpleArithmetic DEF Ballot
    <3>2. SafeAt(b+1,v) = SafeAtProp!(b+1,v)!2
       BY SafeAtProp, <2>1
    <3>3. @ = SafeAtProp!(b+1,v)!2!2
      BY <3>1
    <3>4. @ = \E Q \in Quorum : 
               /\ \A a \in Q : maxBal[a] \geq (b+1)
               /\ \E cc \in -1..b :
                    /\ (cc # -1) => /\ SafeAt(cc, v)
                                    /\ \A a \in Q :
                                         \A w \in Value :
                                            VotedFor(a, cc, w) => (w = v)
                    /\ \A d \in (cc+1)..b, a \in Q : DidNotVoteIn(a, d)
      BY <2>1
    <3>5. QED
      BY <3>2, <3>3, <3>4, <2>3 
  <2>5. PICK cc \in -1..b : 
               /\ (cc # -1) => /\ SafeAt(cc, v)
                               /\ \A a \in Q :
                                     \A w \in Value :
                                        VotedFor(a, cc, w) => (w = v)
               /\ \A d \in (cc+1)..b, a \in Q : DidNotVoteIn(a, d)
    BY <2>4
  <2>6. CASE c > cc
    <3>1. c \in (cc+1)..b
      BY <2>6, SimpleArithmetic DEF Ballot
    <3>2. \A a \in Q : DidNotVoteIn(a, c)
      BY <3>1, <2>5
    <3>3. \A a \in Q : maxBal[a] >= c
      <4> SUFFICES ASSUME NEW a \in Q
                   PROVE  maxBal[a] >= c
        OBVIOUS
      <4>1. \A mbal \in Ballot \cup {-1} : 
               (mbal \geq b+1) => (mbal \geq c)
        BY <3>1, SimpleArithmetic DEF Ballot
      <4>2. maxBal[a] \geq b+1
        BY <2>4
      <4>3. QED 
        BY QA, a \in Acceptor, <4>1, <4>2 DEF TypeOK
    <3>4. QED
      BY <3>2, <3>3
  <2>7. CASE c =< cc
    <3>1. /\ cc \in 0..b
          /\ cc # -1
      BY <2>7, SimpleArithmetic DEF Ballot
    <3>2. SafeLemma!2!(cc)!(v)
      BY <1>2, <3>1
    <3>3. SafeAt(cc, v)
      BY <2>5, <3>1
    <3>4. CASE c = cc
      <4>1. \A mb \in Ballot \cup {-1} : (mb >= b+1) => (mb >= c)
        BY <3>4, <3>1, SimpleArithmetic DEF Ballot
      <4>2. \A a \in Q : maxBal[a] \in Ballot \cup {-1}
        BY QA DEF TypeOK
      <4>3. \A a \in Q : maxBal[a] \geq c
        BY <2>4, <4>1, <4>2
      <4>4. \A a \in Q : \/ DidNotVoteIn(a, c)
                         \/ VotedFor(a, c, v)
        <5> SUFFICES ASSUME NEW a \in Q,
                            ~ DidNotVoteIn(a, c)
                     PROVE  VotedFor(a, c, v)
          OBVIOUS
        <5>1. PICK w \in Value : VotedFor(a, c, w)
          BY DEF DidNotVoteIn
        <5>2. w = v
          BY <3>4, <5>1,  <2>5, <3>1
        <5>3. QED
          BY <5>1, <5>2          
      <4>5. QED
        BY <4>3, <4>4      
    <3>5. CASE c < cc
      <4>1. c \in 0..(cc-1)
        BY <3>1, <3>5, SimpleArithmetic
      <4>2. SafeLemma!2!(cc)
        BY <3>1, <1>2
      <4>3. QED
        BY <4>1,<4>2, <4>2, <3>3
    <3>6. QED
      <4>1. (c < cc) \/ (c = cc)
        BY <2>7, SimpleArithmetic DEF Ballot
      <4>2. QED
        BY <3>4, <3>5, <4>1
  <2>8. QED
    <3>1. c \in Int /\ cc \in Int
      BY SimpleArithmetic DEF Ballot
    <3>2. (c > cc) \/ (c =< cc)
      BY SimpleArithmetic 
    <3>3. QED
      BY <2>6, <2>7, <3>2
<1>3. \A b \in Ballot : P[b]
  BY <1>1, <1>2, SimpleNatInduction DEF Ballot
<1>4. QED
  <2>1. \A b \in Ballot : b \in 0..b
    BY SimpleArithmetic DEF Ballot
  <2>2. QED
    BY <1>3, <2>1
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the invariant that is used to prove the correctness of    *)
(* our algorithm--meaning that specification Spec implements specification *)
(* Spec of module Consensus under our refinement mapping.  Correctness of  *)
(* the voting algorithm follows from the the following three invariants:   *)
(*                                                                         *)
(*   VInv1: In any ballot, an acceptor can vote for at most one value.     *)
(*                                                                         *)
(*   VInv2: An acceptor can vote for a value v in ballot b iff v is        *)
(*          safe at b.                                                     *)
(*                                                                         *)
(*   VInv3: Two different acceptors cannot vote for different values in    *)
(*          the same ballot.                                               *)
(*                                                                         *)
(* Their precise definitions are as follows.                               *)
(***************************************************************************)
VInv1 == \A a \in Acceptor, b \in Ballot, v, w \in Value : 
           VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

VInv2 == \A a \in Acceptor, b \in Ballot, v \in Value :
                  VotedFor(a, b, v) => SafeAt(b, v)

VInv3 ==  \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
                VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

(***************************************************************************)
(* It is obvious, that VInv3 implies VInv1--a fact that we now let TLAPS   *)
(* prove as a little check that we haven't made a mistake in our           *)
(* definitions.  (Actually, we used TLC to check everything before         *)
(* attempting any proofs.) We define VInv1 separately because VInv3 is not *)
(* needed for proving safety, only for liveness.                           *)
(***************************************************************************)
THEOREM VInv3 => VInv1
BY DEF VInv1, VInv3
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma proves that SafeAt(b, v) implies that no value      *)
(* other than v can have been chosen in any ballot numbered less than b.   *)
(* The fact that it also implies that no value other than v can ever be    *)
(* chosen in the future follows from this and the fact that SafeAt(b, v)   *)
(* is stable--meaning that once it becomes true, it remains true forever.  *)
(* The stability of SafeAt(b, v) is proved as step <1>6 of theorem         *)
(* InductiveInvariance below.                                              *)
(*                                                                         *)
(* This lemma is used only in the proof of theorem VT1 below.              *)
(***************************************************************************)
LEMMA VT0 == /\ TypeOK
             /\ VInv1
             /\ VInv2
             => \A v, w \in Value, b, c \in Ballot : 
                   (b > c) /\ SafeAt(b, v) /\ ChosenIn(c, w) => (v = w)
<1> SUFFICES ASSUME TypeOK, VInv1, VInv2,
                    NEW v \in Value, NEW w \in Value 
             PROVE  \A b, c \in Ballot : 
                      (b > c) /\ SafeAt(b, v) /\ ChosenIn(c, w) => (v = w)
  OBVIOUS
<1> P == [b \in Ballot |-> 
            \A c \in Ballot : 
            (b > c) /\ SafeAt(b, v) /\ ChosenIn(c, w) => (v = w)]

<1>1. P[0]
  <2>1. /\ 0 \in Ballot 
        /\ \A c \in Ballot : ~(0 > c)
    BY SimpleArithmetic DEF Ballot
  <2>2. QED
    BY <2>1
<1>2. ASSUME NEW b \in Ballot, \A i \in 0..b : P[i]
      PROVE  P[b+1]
  <2>1. b+1 \in Ballot
    BY SimpleArithmetic DEF Ballot
  <2>2. SUFFICES ASSUME NEW c \in Ballot, b+1 > c, SafeAt(b+1, v), ChosenIn(c, w)
                 PROVE  v=w
    BY <2>1
  <2>3. PICK Q \in Quorum : \A a \in Q : VotedFor(a, c, w)
    BY <2>2 DEF ChosenIn
  <2>4. b+1 # 0 /\ ((b+1)-1 = b) 
    BY SimpleArithmetic DEF Ballot
  <2>5. PICK QQ \in Quorum, 
              d \in -1..((b+1)-1) :
                /\ (d # -1) => /\ SafeAt(d, v)
                               /\ \A a \in QQ :
                                    \A x \in Value :
                                        VotedFor(a, d, x) => (x = v)
                /\ \A e \in (d+1)..((b+1)-1), a \in QQ : DidNotVoteIn(a, e)
   BY <2>1, <2>2, <2>4, SafeAtProp
  <2> PICK aa \in QQ \cap Q : TRUE
    BY QA
  <2>6. c \leq d 
    <3>1. SUFFICES ASSUME ~(c \leq d)
                 PROVE  FALSE
      OBVIOUS
    <3>2. c \in (d+1)..((b+1)-1)
      BY <2>2, <3>1, SimpleArithmetic DEF Ballot
    <3>3. VotedFor(aa, c, w)
      BY <2>3
    <3>4. DidNotVoteIn(aa, c)
      BY <2>5, <3>1, <3>2
    <3>5. QED
      BY <3>3, <3>4 DEF DidNotVoteIn
  <2>7. d # -1
    BY <2>6, SimpleArithmetic DEF Ballot
  <2>8. CASE c = d
    BY <2>3, <2>5, <2>7, <2>8
  <2>9. CASE d > c
    <3>1. SafeAt(d, v)
      BY <2>5, <2>7
    <3>2. d \in Ballot /\ d \in 0..b 
      BY <2>6, SimpleArithmetic DEF Ballot
    <3>3. P[d]
      BY <1>2, <3>2
    <3>4. QED
      BY <2>2, <2>9, <3>1,  <3>2, <3>3
  <2>10. QED
    <3>1. (c = d) \/ (d > c)
      BY <2>6, SimpleArithmetic DEF Ballot
    <3>2. QED
      BY <2>8, <2>9, <3>1
\*  PICK QQ \in Quorum  : VotedFor(ac, c, w)
\*  BY QuorumNonEmpty, QA DEF ChosenIn
<1>3. \A b \in Ballot : P[b]
  BY <1>1, <1>2, GeneralNatInduction DEF Ballot

<1>4. QED
  BY <1>3
 
(***************************************************************************)
(* The following theorem asserts that the invariance of TypeOK, VInv1, and *)
(* VInv2 implies that the algorithm satisfies the basic consensus property *)
(* that at most one value is chosen (at any time).  If you can prove it,   *)
(* then you understand why the Paxos consensus algorithm allows only a     *)
(* single value to be chosen.  Note that VInv3 is not needed to prove this *)
(* property.                                                               *)
(***************************************************************************)
THEOREM VT1 == /\ TypeOK 
               /\ VInv1
               /\ VInv2
               => \A v, w : 
                    (v \in chosen) /\ (w \in chosen) => (v = w)
<1>1. SUFFICES ASSUME TypeOK, VInv1, VInv2,
                      NEW v, NEW w, 
                      v \in chosen, w \in chosen
               PROVE  v = w
  OBVIOUS
<1>2. v \in Value /\ w \in Value
  BY <1>1 DEF chosen
<1>3. PICK b \in Ballot, c \in Ballot : ChosenIn(b, v) /\ ChosenIn(c, w)
  BY <1>1 DEF chosen
<1>4. PICK Q \in Quorum, R \in Quorum : 
         /\ \A a \in Q : VotedFor(a, b, v)
         /\ \A a \in R : VotedFor(a, c, w)
  BY <1>3 DEF ChosenIn
<1>5. PICK av \in Q, aw \in R: /\ VotedFor(av, b, v)
                               /\ VotedFor(aw, c, w)
  BY <1>4, QuorumNonEmpty
<1>6. SafeAt(b, v) /\ SafeAt(c, w)
  BY <1>1, <1>2, <1>5, QA DEF VInv2
<1>7. CASE b = c
  <2> PICK a \in Q \cap R : TRUE
    BY QA
  <2>1. /\ VotedFor(a, b, v)
        /\ VotedFor(a, c, w)
    BY <1>4
  <2>2. QED
    BY <1>1, <1>2, <1>7, <2>1, QA DEF VInv1
<1>8. CASE b > c
  BY <1>1, <1>6, <1>3, <1>8, VT0, <1>2 \* <2>1
<1>9. CASE c > b
    BY <1>1, <1>6, <1>3, <1>9, VT0, <1>2 \* <2>1
<1>10. QED
  <2>1. (b = c) \/ (b > c) \/ (c > b)
    BY SimpleArithmetic DEF Ballot
  <2>2. QED
    BY <1>7, <1>8, <1>9, <2>1

(***************************************************************************)
(* The rest of the proof uses only the primed version of VT1--that is, the *)
(* theorem whose statement is VT1'.  (Remember that VT1 names the formula  *)
(* being asserted by the theorem we call VT1.) The formula VT1' asserts    *)
(* that VT1 is true in the second state of any transition (pair of         *)
(* states).  Since the proof of theorem VT1 shows that VT1 is true in any  *)
(* state, formula VT1' is obviously true for any transition.  However,     *)
(* proving this requires a kind of reasoning that distinguishes between    *)
(* inference and implication.  If the difference between inference and     *)
(* implication means nothing to you, it is because that difference does    *)
(* not arise in ordinary logic; it becomes important only in modal logics. *)
(* (Temporal logic is one example of modal logic.) Because TLAPS does not  *)
(* yet handle any modal-logic reasoning, it is yet able to deduce VT1'     *)
(* from VT1.  This ability will be added when TLAPS is enhanced to do      *)
(* temporal-logic reasoning.  For now, we have write a separate theorem,   *)
(* whose proof is obtained from that of VT1 by priming everything.  We     *)
(* also need the primed versions of SafeAtProp and VT0, which are used in  *)
(* its proof.                                                              *)
(*                                                                         *)
(* The proof of the primed version of a theorem is obtained by simply      *)
(* priming all the steps in the proof of the original theorem (replacing   *)
(* references to lemmas by references to their primed versions).  Since we *)
(* did not prove SafeAtProp, we cannot prove its primed version either.    *)
(***************************************************************************)
THEOREM SafeAtPropPrime ==
  \A b \in Ballot, v \in Value :
    SafeAt(b, v)' =
      \/ b = 0
      \/ \E Q \in Quorum :
           /\ \A a \in Q : maxBal'[a] \geq b
           /\ \E c \in -1..(b-1) :
                /\ (c # -1) => /\ SafeAt(c, v)'
                               /\ \A a \in Q :
                                    \A w \in Value :
                                        VotedFor(a, c, w)' => (w = v)
                /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)'
PROOF OMITTED

LEMMA VT0Prime ==
             /\ TypeOK'
             /\ VInv1'
             /\ VInv2'
             => \A v, w \in Value, b, c \in Ballot : 
                   (b > c) /\ SafeAt(b, v)' /\ ChosenIn(c, w)' => (v = w)
<1> SUFFICES ASSUME TypeOK', VInv1', VInv2',
                    NEW v \in Value, NEW w \in Value 
             PROVE  \A b, c \in Ballot : 
                      (b > c) /\ SafeAt(b, v)' /\ ChosenIn(c, w)' => (v = w)
  OBVIOUS
<1> P == [b \in Ballot |-> 
            \A c \in Ballot : 
            (b > c) /\ SafeAt(b, v)' /\ ChosenIn(c, w)' => (v = w)]

<1>1. P[0]
  <2>1. /\ 0 \in Ballot 
        /\ \A c \in Ballot : ~(0 > c)
    BY SimpleArithmetic DEF Ballot
  <2>2. QED
    BY <2>1
<1>2. ASSUME NEW b \in Ballot, \A i \in 0..b : P[i]
      PROVE  P[b+1]
  <2>1. b+1 \in Ballot
    BY SimpleArithmetic DEF Ballot
  <2>2. SUFFICES ASSUME NEW c \in Ballot, b+1 > c, SafeAt(b+1, v)', ChosenIn(c, w)'
                 PROVE  v=w
    BY <2>1
  <2>3. PICK Q \in Quorum : \A a \in Q : VotedFor(a, c, w)'
    BY <2>2 DEF ChosenIn
  <2>4. b+1 # 0 /\ ((b+1)-1 = b) 
    BY SimpleArithmetic DEF Ballot
  <2>5. PICK QQ \in Quorum, 
              d \in -1..((b+1)-1) :
                /\ (d # -1) => /\ SafeAt(d, v)'
                               /\ \A a \in QQ :
                                    \A x \in Value :
                                        VotedFor(a, d, x)' => (x = v)
                /\ \A e \in (d+1)..((b+1)-1), a \in QQ : DidNotVoteIn(a, e)'
   BY <2>1, <2>2, <2>4, SafeAtPropPrime
  <2> PICK aa \in QQ \cap Q : TRUE
    BY QA
  <2>6. c \leq d 
    <3>1. SUFFICES ASSUME ~(c \leq d)
                 PROVE  FALSE
      OBVIOUS
    <3>2. c \in (d+1)..((b+1)-1)
      BY <2>2, <3>1, SimpleArithmetic DEF Ballot
    <3>3. VotedFor(aa, c, w)'
      BY <2>3
    <3>4. DidNotVoteIn(aa, c)'
      BY <2>5, <3>1, <3>2
    <3>5. QED
      BY <3>3, <3>4 DEF DidNotVoteIn
  <2>7. d # -1
    BY <2>6, SimpleArithmetic DEF Ballot
  <2>8. CASE c = d
    BY <2>3, <2>5, <2>7, <2>8
  <2>9. CASE d > c
    <3>1. SafeAt(d, v)'
      BY <2>5, <2>7
    <3>2. d \in Ballot /\ d \in 0..b 
      BY <2>6, SimpleArithmetic DEF Ballot
    <3>3. P[d]
      BY <1>2, <3>2
    <3>4. QED
      BY <2>2, <2>9, <3>1,  <3>2, <3>3
  <2>10. QED
    <3>1. (c = d) \/ (d > c)
      BY <2>6, SimpleArithmetic DEF Ballot
    <3>2. QED
      BY <2>8, <2>9, <3>1
\*  PICK QQ \in Quorum  : VotedFor(ac, c, w)
\*  BY QuorumNonEmpty, QA DEF ChosenIn
<1>3. \A b \in Ballot : P[b]
  BY <1>1, <1>2, GeneralNatInduction DEF Ballot

<1>4. QED
  BY <1>3

THEOREM VT1Prime == 
               /\ TypeOK' 
               /\ VInv1'
               /\ VInv2'
               => \A v, w : 
                    (v \in chosen') /\ (w \in chosen') => (v = w)
<1>1. SUFFICES ASSUME TypeOK', VInv1', VInv2',
                      NEW v, NEW w, 
                      v \in chosen', w \in chosen'
               PROVE  v = w
  OBVIOUS
<1>2. v \in Value /\ w \in Value
  BY <1>1 DEF chosen
<1>3. PICK b \in Ballot, c \in Ballot : ChosenIn(b, v)' /\ ChosenIn(c, w)'
  BY <1>1 DEF chosen
<1>4. PICK Q \in Quorum, R \in Quorum : 
         /\ \A a \in Q : VotedFor(a, b, v)'
         /\ \A a \in R : VotedFor(a, c, w)'
  BY <1>3 DEF ChosenIn
<1>5. PICK av \in Q, aw \in R: /\ VotedFor(av, b, v)'
                               /\ VotedFor(aw, c, w)'
  BY <1>4, QuorumNonEmpty
<1>6. SafeAt(b, v)' /\ SafeAt(c, w)'
  BY <1>1, <1>2, <1>5, QA DEF VInv2
<1>7. CASE b = c
  <2> PICK a \in Q \cap R : TRUE
    BY QA
  <2>1. /\ VotedFor(a, b, v)'
        /\ VotedFor(a, c, w)'
    BY <1>4
  <2>2. QED
    BY <1>1, <1>2, <1>7, <2>1, QA DEF VInv1
<1>8. CASE b > c
  BY <1>1, <1>6, <1>3, <1>8, VT0Prime, <1>2 \* <2>1
<1>9. CASE c > b
    BY <1>1, <1>6, <1>3, <1>9, VT0Prime, <1>2 \* <2>1
<1>10. QED
  <2>1. (b = c) \/ (b > c) \/ (c > b)
    BY SimpleArithmetic DEF Ballot
  <2>2. QED
    BY <1>7, <1>8, <1>9, <2>1
-----------------------------------------------------------------------------
(***************************************************************************)
(* The invariance of VInv2 depends on SafeAt(b, v) being stable, meaning   *)
(* that once it becomes true it remains true forever.  Stability of        *)
(* SafeAt(b, v) depends on the following invariant.                        *)
(***************************************************************************)
VInv4 == \A a \in Acceptor, b \in Ballot : 
            maxBal[a] < b => DidNotVoteIn(a, b)
             
(***************************************************************************)
(* The inductive invariant that we use to prove correctness of this        *)
(* algorithm is VInv, defined as follows.                                  *)
(***************************************************************************)
VInv == TypeOK /\ VInv2 /\ VInv3 /\ VInv4
-----------------------------------------------------------------------------
(***************************************************************************)
(* To simplify reasoning about the next-state action Next, we want to      *)
(* express it in a more convenient form.  This is done by lemma NextDef    *)
(* below, which shows that Next equals an action defined in terms of the   *)
(* following subactions.                                                   *)
(***************************************************************************)
IncreaseMaxBal(self, b) ==  
  /\ b > maxBal[self]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ UNCHANGED votes

VoteFor(self, b, v) == 
  /\ maxBal[self] \leq b
  /\ DidNotVoteIn(self, b)
  /\ \A p \in Acceptor \ {self} :
        \A w \in Value : VotedFor(p, b, w) => (w = v)
  /\ SafeAt(b, v)
  /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]

BallotAction(self, b) ==
  \/ IncreaseMaxBal(self, b)
  \/ \E v \in Value : VoteFor(self, b, v)

(***************************************************************************)
(* When proving lemma NextDef, we were surprised to discover that it       *)
(* required the assumption that the set of acceptors is non-empty.  This   *)
(* assumption isn't necessary for safety, since if there are no acceptors  *)
(* there can be no quorums (see theorem QuorumNonEmpty above) so no value  *)
(* is ever chosen and the Consensus specification is trivially implemented *)
(* under our refinement mapping.  However, the assumption is necessary for *)
(* liveness and it allows us to lemma NextDef for the safety proof as      *)
(* well, so we assert it now.                                              *)
(***************************************************************************)
ASSUME AcceptorNonempty == Acceptor # {}

(***************************************************************************)
(* The proof of the lemma itself is quite simple.                          *)
(***************************************************************************)
LEMMA NextDef ==
  TypeOK => 
   (Next =  \E self \in Acceptor :
                 \E b \in Ballot : BallotAction(self, b) )
<1> HAVE TypeOK
<1>2. Next = \E self \in Acceptor: acceptor(self)
 BY AcceptorNonempty DEF Next, ProcSet
<1>3. @ = NextDef!2!2
  BY DEF Next, BallotAction, IncreaseMaxBal, VoteFor, ProcSet, acceptor
<1>4. QED  
  BY <1>2, <1>3
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now come to the proof that VInv is an invariant of the               *)
(* specification.  This follows from the following result, which asserts   *)
(* that it is an inductive invariant of the next-state action.  This fact  *)
(* is used in the liveness proof as well.                                  *)
(***************************************************************************)
THEOREM InductiveInvariance == VInv /\ [Next]_vars => VInv'
<1>1. VInv /\ (vars' = vars) => VInv'
  <2> SUFFICES ASSUME VInv, vars' = vars
               PROVE  VInv'
    OBVIOUS
  <2> USE DEF vars, VInv
  <2>1. TypeOK'
    BY DEF TypeOK
  <2>2. VInv2'
    BY DEF VInv2, VotedFor, SafeAt, DidNotVoteIn
  <2>3. VInv3'
    BY DEF VInv3, VotedFor
  <2>4. VInv4'
    BY DEF VInv4, DidNotVoteIn, VotedFor
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 

<1> SUFFICES ASSUME VInv, 
                    NEW self \in Acceptor,
                    NEW b \in Ballot, 
                    BallotAction(self, b)
             PROVE  VInv'
  BY <1>1, NextDef DEF VInv

<1>2. TypeOK'
  <2>1. CASE IncreaseMaxBal(self, b)
    BY <2>1 DEF IncreaseMaxBal, VInv, TypeOK
  <2>2. CASE \E v \in Value : VoteFor(self, b, v)
    BY <2>2 DEF VInv, TypeOK, VoteFor
  <2>3. QED
    BY <2>1, <2>2 DEF BallotAction

<1>3. ASSUME NEW a \in Acceptor, NEW c \in Ballot, NEW w \in Value,
             VotedFor(a, c, w)
      PROVE  VotedFor(a, c, w)'
  <2>1. CASE IncreaseMaxBal(self, b)
    BY <2>1, <1>3 DEF IncreaseMaxBal, VotedFor
  <2>2. CASE \E v \in Value : VoteFor(self, b, v)
    <3>1. PICK v \in Value : VoteFor(self, b, v)
      BY <2>2
    <3>2. CASE a = self
      <4>1. votes'[a] = votes[a] \cup {<<b, v>>}
        BY <3>1, <3>2 DEF VoteFor, VInv, TypeOK
      <4>2. QED
        BY <1>3, <4>1 DEF VotedFor
    <3>3. CASE a # self
      <4>1. votes[a] = votes'[a] 
        BY <3>1, <3>3 DEF VoteFor, VInv, TypeOK
      <4>2. QED
        BY <1>3, <4>1 DEF VotedFor
    <3>4. QED
     BY <3>2, <3>3 DEF VoteFor
  <2>3. QED
    BY <2>1, <2>2 DEF BallotAction

<1>4. ASSUME NEW a \in Acceptor, NEW c \in Ballot, NEW w \in Value,
             ~VotedFor(a, c, w), VotedFor(a, c, w)'
      PROVE  (a = self) /\ (c = b) /\ VoteFor(self, b, w) 
  <2>1. CASE IncreaseMaxBal(self, b)
      BY <2>1, <1>4 DEF IncreaseMaxBal, VInv, TypeOK, VotedFor
  <2>2. CASE \E v \in Value : VoteFor(self, b, v)
    <3>1. PICK v \in Value : VoteFor(self, b, v)
      BY <2>2
    <3>2. a = self
      <4> SUFFICES ASSUME a # self
                   PROVE  FALSE
        OBVIOUS
      <4>1. votes'[a] = votes[a]
        BY <3>1 DEF VoteFor, VInv, TypeOK
      <4>2. QED
        BY <4>1, <1>4 DEF VotedFor 
    <3>3. votes'[a] = votes[a] \cup {<<b, v>>}
      BY <3>1, <3>2 DEF VoteFor, VInv, TypeOK
    <3>4. c = b /\ v = w
      BY <1>4, <3>3 DEF VotedFor
    <3>5. QED
      BY <3>1, <3>2, <3>4
  <2>3. QED
    BY <2>1, <2>2 DEF BallotAction
    

<1>5. ASSUME NEW a \in Acceptor
      PROVE  /\ maxBal[a] \in Ballot \cup {-1}
             /\ maxBal'[a] \in Ballot \cup {-1}
             /\ maxBal'[a] >= maxBal[a]
  <2>1. /\ maxBal[a] \in Ballot \cup {-1}
        /\ maxBal'[a] \in Ballot \cup {-1}
    BY <1>2 DEF VInv, TypeOK
  <2>2. /\ (a = self) => /\ maxBal'[a] = b 
                         /\ \/ b > maxBal[a]
                            \/ maxBal[a] \leq b
        /\ (a # self) => (maxBal'[a] = maxBal[a])
    <3>1. CASE IncreaseMaxBal(self, b)
      BY <3>1 DEF IncreaseMaxBal, VInv, TypeOK
    <3>2. CASE \E v \in Value : VoteFor(self, b, v)
      BY <3>2 DEF VoteFor, VInv, TypeOK
    <3>3. QED
      BY <3>1, <3>2 DEF BallotAction
  <2>3. \A mb \in Ballot \cup {-1} : /\ (b > mb) => (b >= mb)
                                     /\ mb >= mb
    BY SimpleArithmetic DEF Ballot
  <2>4. QED
    BY <2>1, <2>2, <2>3
    
<1>6. ASSUME NEW c \in Ballot, NEW w \in Value,
             SafeAt(c, w)
      PROVE  SafeAt(c, w)'
  <2> DEFINE P[i \in Ballot] == \A j \in 0..i : SafeAt(j, w) => SafeAt(j, w)'
  <2>1. P[0]
    <3>1. 0 \in Ballot /\ \A i \in 0..0 : i = 0
      BY SimpleArithmetic DEF Ballot
    <3>2. QED
      BY SafeAtPropPrime, <3>1
  <2>2. ASSUME NEW d \in Ballot, P[d]
        PROVE  P[d+1]
    <3>1. d+1 \in Ballot /\ d+1 # 0
      BY SimpleArithmetic DEF Ballot
    <3>2. SUFFICES ASSUME NEW e \in 0..(d+1), SafeAt(e, w)
                   PROVE  SafeAt(e, w)'
      BY <3>1
    <3>3. e \in 0..d \/ e = d+1
      BY SimpleArithmetic DEF Ballot
    <3>4. CASE e \in 0..d
      BY <2>2, <3>2, <3>4
    <3>5. CASE e = d+1
      <4>1. PICK Q \in Quorum : SafeAtProp!(e, w)!2!2!(Q)
        BY <3>1, <3>2, <3>5, SafeAtProp
      <4>2. \A aa \in Q : maxBal'[aa] \geq e
        <5>1. SUFFICES ASSUME NEW aa \in Q
                       PROVE  maxBal'[aa] \geq e
          OBVIOUS
        <5>2. \A mbp, mb \in Ballot \cup {-1} : 
                 mbp >= mb /\ mb >= e => mbp >= e
          BY SimpleArithmetic DEF Ballot
        <5>3. QED
          BY <5>2, <1>5, <4>1, QA
      <4>3. \E cc \in -1..(e-1) : 
               /\ (cc # -1) => /\ SafeAt(cc, w)'
                               /\ \A ax \in Q :
                                    \A z \in Value :
                                        VotedFor(ax, cc, z)' => (z = w)
               /\ \A dd \in (cc+1)..(e-1), ax \in Q : DidNotVoteIn(ax, dd)'
        <5>1. ASSUME NEW cc \in 0..(e-1),
                     NEW ax \in Q, NEW z \in Value, 
                     VotedFor(ax, cc, z)', ~ VotedFor(ax, cc, z)
              PROVE  FALSE
          <6>1. cc \in Ballot
            BY <5>1, <3>5, SimpleArithmetic DEF Ballot
          <6>2. (ax = self) /\ (cc = b) /\ VoteFor(self, b, z)
            BY <5>1, <6>1, <1>4, QA
          <6>3. maxBal[ax] \geq e
            BY <4>1 
          <6>4. maxBal[self] \leq b
            BY <6>2 DEF VoteFor
          <6>5. \A mb \in Ballot \cup {-1} : ~ (mb \geq e /\ mb \leq b)
            BY <3>5, <6>2, SimpleArithmetic DEF Ballot
          <6>6. QED
            BY <6>2, <6>3, <6>4, <6>5 DEF VInv, TypeOK
        <5>2. PICK cc \in -1..(e-1) : SafeAtProp!(e, w)!2!2!(Q)!2!(cc)
          BY <4>1
        <5>3. (cc # -1) => /\ SafeAt(cc, w)'
                           /\ \A ax \in Q :
                                    \A z \in Value :
                                        VotedFor(ax, cc, z)' => (z = w)
          <6>1. SUFFICES ASSUME cc # -1
                         PROVE  /\ SafeAt(cc, w)'
                                /\ \A ax \in Q :
                                     \A z \in Value :
                                        VotedFor(ax, cc, z)' => (z = w)
            OBVIOUS
          <6>2. /\ SafeAt(cc, w)
                /\ \A ax \in Q :
                     \A z \in Value : VotedFor(ax, cc, z) => (z = w)
            BY <5>2, <6>1
          <6>3. SafeAt(cc, w)'
            <7>1. cc \in 0..d /\ cc \in Ballot
              BY <6>1, <3>5, SimpleArithmetic DEF Ballot
            <7>2. QED
              BY <2>2, <6>2, <7>1
          <6>4. ASSUME NEW ax \in Q, NEW z \in Value, VotedFor(ax, cc, z)'
                PROVE  z = w
            <7>1. CASE VotedFor(ax, cc, z)
              BY <6>2, <7>1
            <7>2. CASE ~ VotedFor(ax, cc, z)
              <8>1. cc \in 0..(e-1)
                BY <6>1, SimpleArithmetic DEF Ballot
              <8>2 QED
                BY <8>1, <7>2, <6>4, <5>1               
            <7>3. QED
              BY <7>1, <7>2
          <6>5. QED
            BY <6>3, <6>4
        <5>4. \A dd \in (cc+1)..(e-1), ax \in Q : DidNotVoteIn(ax, dd)'
          <6>1. SUFFICES ASSUME NEW dd \in (cc+1)..(e-1), NEW ax \in Q,
                                ~ DidNotVoteIn(ax, dd)'
                         PROVE  FALSE
            OBVIOUS
          <6>2. DidNotVoteIn(ax, dd)
            BY <5>2
          <6>3. PICK v \in Value : VotedFor(ax, dd, v)'
            BY <6>1 DEF DidNotVoteIn
          <6>4. dd \in 0..(e-1)
            BY SimpleArithmetic DEF Ballot
          <6>5. QED
            BY <6>2, <6>3, <6>4, <5>1 DEF DidNotVoteIn
        <5>5. QED
          BY <5>3, <5>4
      <4>4.  \/ e = 0
             \/ \E Q_1 \in Quorum :
                   /\ \A aa \in Q_1 : maxBal'[aa] \geq e
                   /\ \E c_1 \in -1..e - 1 :
                         /\ c_1 # -1
                            => (/\ SafeAt(c_1, w)'
                                /\ \A aa \in Q_1 :
                                      \A w_1 \in Value :
                                         VotedFor(aa, c_1, w_1)' => w_1 = w)
                         /\ \A d_1 \in c_1 + 1..e - 1, aa \in Q_1 :
                               DidNotVoteIn(aa, d_1)'
         BY <4>2, <4>3, <3>1, <3>5
      <4>5. e \in Ballot
        BY <3>1, <3>5
      <4>6. SafeAt(e, w)' = <4>4
        BY SafeAtPropPrime, <4>5
      <4>7. QED
        BY <4>2, <4>3, <4>6 
    <3>6. QED
      BY <3>3, <3>4, <3>5
  <2>3. \A d \in Ballot : P[d]
    BY <2>1, <2>2, SimpleNatInduction DEF Ballot
  <2>4. QED
    <3>1. c \in 0..c
      BY SimpleArithmetic DEF Ballot
    <3>2. QED
      BY <2>3, <3>1, <1>6

<1>7. VInv2'
  <2>1. SUFFICES ASSUME NEW a \in Acceptor, NEW c \in Ballot, NEW v \in Value,
                        VotedFor(a, c, v)'
                 PROVE  SafeAt(c, v)'
    BY DEF VInv2
  <2>2. CASE VotedFor(a, c, v)
    BY <1>6, <2>2 DEF VInv, VInv2
  <2>3. CASE ~VotedFor(a, c, v)
    <3>1. (a = self) /\ (c = b) /\ VoteFor(self, b, v)
      BY <2>1, <2>3, <1>4
    <3>2. SafeAt(c, v)
      BY <3>1 DEF VoteFor
    <3>3. QED
      BY <3>2, <1>6
  <2>4. QED
    BY <2>2, <2>3

<1>8. VInv3'
  <2>1. ASSUME NEW a1 \in Acceptor, NEW a2\in Acceptor, 
               NEW c \in Ballot,    NEW v1 \in Value, NEW v2 \in Value, 
               VotedFor(a1, c, v1)', 
               VotedFor(a2, c, v2)',
               VotedFor(a1, c, v1),
               VotedFor(a2, c, v2)
         PROVE v1 = v2
    BY <2>1 DEF VInv, VInv3
  <2>2. ASSUME NEW a1 \in Acceptor, NEW a2\in Acceptor, 
               NEW c \in Ballot,    NEW v1 \in Value, NEW v2 \in Value, 
               VotedFor(a1, c, v1)', 
               VotedFor(a2, c, v2)',
               ~ VotedFor(a1, c, v1)
         PROVE v1 = v2
    <3>1. (a1 = self) /\ (c = b) /\ VoteFor(self, b, v1)
      BY <2>2, <1>4
    <3>2. CASE a2 = self
      <4>1. ~VotedFor(self, b, v2)
        BY <3>1 DEF VoteFor, DidNotVoteIn
      <4>2. VoteFor(self, b, v2)
        BY <2>2, <3>1, <3>2, <4>1,  <1>4
      <4>3. votes'[self] = votes[self] \cup {<<b, v1>>}
        BY <3>1 DEF VoteFor, VInv, TypeOK
      <4>4. votes'[self] = votes[self] \cup {<<b, v2>>}
        BY <4>2 DEF VoteFor, VInv, TypeOK
      <4>5. <<b, v1>> \notin votes[self]
        BY <2>2, <3>1 DEF VotedFor
      <4>6. QED
        <5>1. <<b, v1>> \in votes[self] \cup {<<b, v2>>}
          BY <4>3, <4>4
        <5>2. QED
        BY <5>1, <4>5
    <3>3. CASE a2 # self
      <4>1. votes'[a2] = votes[a2]
        BY <3>1, <3>3 DEF VoteFor, VInv, TypeOK
      <4>2. VotedFor(a2, b, v2)
        BY <2>2, <3>1, <4>1 DEF VotedFor
      <4>3. QED
        BY <3>1, <3>3, <4>2 DEF VoteFor \* SMT fails
    <3>4. QED
      BY <3>2, <3>3
  <2>3. QED
    BY <2>1, <2>2 DEF VInv3

<1>9. VInv4'
  <2>1. SUFFICES ASSUME NEW a \in Acceptor, NEW c \in Ballot, 
                        maxBal'[a] < c, 
                        ~ DidNotVoteIn(a, c)'
                 PROVE  FALSE
    BY DEF VInv4
  <2>2. maxBal[a] < c
    <3>1. \A x, xp \in Ballot \cup {-1} : xp < c /\ xp >= x => x < c
      BY SimpleArithmetic DEF Ballot \* SMT fails
    <3>2. QED
      BY <1>5, <2>1,  <3>1  \* SMT fails 
  <2>3. DidNotVoteIn(a, c)
    BY <2>2 DEF VInv, VInv4
  <2>4. PICK v \in Value : VotedFor(a, c, v)'
    BY <2>1 DEF DidNotVoteIn
  <2>5. (a = self) /\ (c = b) /\ VoteFor(self, b, v)
    BY <1>4, <2>1, <2>3, <2>4 DEF DidNotVoteIn
  <2>6. maxBal'[a] = c
    BY <2>5 DEF VoteFor, VInv, TypeOK
  <2>7. QED
    <3>1. ~(c < c)
      BY  SimpleArithmetic DEF Ballot \* SMT fails
    <3>2. QED
      BY <2>1, <2>6, <3>1 \* SMT fails  

<1>10. QED
  BY <1>2, <1>7, <1>8, <1>9 DEF VInv

(***************************************************************************)
(* The invariance of VInv follows easily from theorem InductiveInvariance  *)
(* and the following result, which is easy to prove with TLAPS.            *)
(***************************************************************************)
THEOREM InitImpliesInv == Init => VInv
<1> SUFFICES ASSUME Init PROVE VInv
  OBVIOUS
<1> USE DEF Init
<1>1. TypeOK
  BY DEF TypeOK, ProcSet
<1>2. VInv2
  BY  DEF VInv2, VotedFor
<1>3. VInv3
  BY DEF VInv3, VotedFor
<1>4. VInv4
  BY DEF VInv4, DidNotVoteIn, VotedFor
<1>5. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF VInv

(***************************************************************************)
(* The following theorem asserts that VInv is an invariant of Spec.        *)
(* Because TLAPS does not yet do any temporal reasoning, we have to omit   *)
(* the proof of all steps that assert temporal logic formulas.  Both the   *)
(* steps of this trivial proof are therefore omitted.  However, for all    *)
(* such omitted proofs, we give the proof that we expect to be             *)
(* approximately a proof that TLAPS will accept once it does handle        *)
(* temporal logic reasoning.                                               *)
(***************************************************************************)
THEOREM VT2 == Spec => []VInv
<1>1. VInv /\ [][Next]_vars => []VInv
\*  BY InductiveInvariance, RuleINV1
  PROOF OMITTED
<1>2. QED
\*  BY InitImpliesInv, <1>1
  PROOF OMITTED
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following INSTANCE statement instantiates module Consensus with the *)
(* following expressions substituted for the parameters (the CONSTANTS and *)
(* VARIABLES) of that module:                                              *)
(*                                                                         *)
(*   Parameter of Consensus    Expression (of this module)                 *)
(*   ----------------------    ---------------------------                 *)
(*    Value                     Value                                      *)
(*    chosen                    chosen                                     *)
(*                                                                         *)
(* (Note that if no substitution is specified for a parameter, the default *)
(* is to substitute the parameter or defined operator of the same name.)   *)
(* More precisely, for each defined identifier id of module Consensus,     *)
(* this statement defines C!id to equal the value of id under these        *)
(* substitutions.                                                          *)
(***************************************************************************)
C == INSTANCE Consensus 

(***************************************************************************)
(* The following theorem asserts that the safety properties of the voting  *)
(* algorithm (specified by formula Spec) of this module implement the      *)
(* consensus safety specification Spec of module Consensus under the       *)
(* substitution (refinement mapping) of the INSTANCE statement.            *)
(***************************************************************************)
THEOREM VT3 == Spec => C!Spec 
<1>1. Init => C!Init
  <2> SUFFICES ASSUME Init
               PROVE  C!Init
    OBVIOUS
  <2>1. SUFFICES ASSUME chosen # {}
                 PROVE  FALSE
    BY DEF C!Init
  <2>2. PICK v \in chosen : TRUE
    BY <2>1
  <2>3. PICK b \in Ballot : ChosenIn(b, v)
    BY <2>2 DEF chosen
  <2>4. PICK Q \in Quorum : \A a \in Q : VotedFor(a, b, v)
    BY <2>3 DEF ChosenIn
  <2>5. PICK a \in Q : <<b, v>> \in votes[a] \* VotedFor(a, b, v)
    BY QuorumNonEmpty, <2>4 DEF VotedFor
  <2>6. QED
    BY <2>5, QA DEF Init 

<1>2. ASSUME VInv, VInv', [Next]_vars
      PROVE  [C!Next]_C!vars
  <2> USE VInv
  <2>1. CASE vars' = vars
    BY <2>1 DEF vars, C!vars, chosen, ChosenIn, VotedFor
  <2>2. SUFFICES ASSUME NEW self \in Acceptor,
                        NEW b \in Ballot, 
                        BallotAction(self, b)
                 PROVE  [C!Next]_C!vars
    BY <1>2, <2>1, NextDef DEF VInv 
  <2>3. ASSUME IncreaseMaxBal(self, b)
        PROVE  C!vars' = C!vars
    BY <2>3 DEF IncreaseMaxBal, C!vars, chosen, ChosenIn, VotedFor
  <2>4. ASSUME NEW v \in Value,
               VoteFor(self, b, v)
        PROVE  [C!Next]_C!vars
    <3>3. ASSUME NEW w \in chosen
          PROVE  w \in chosen'
      <4>1. PICK c \in Ballot : ChosenIn(c, w)
        BY <3>3 DEF chosen
      <4>2. PICK Q \in Quorum : \A a \in Q : <<c, w>> \in votes[a] 
        BY <4>1 DEF ChosenIn, VotedFor
      <4>3. SUFFICES ASSUME NEW a \in Q
                     PROVE  <<c, w>> \in votes'[a] 
        BY DEF chosen, ChosenIn, VotedFor
      <4>4. CASE a = self
        <6>1. votes'[self] = votes[self] \cup {<<b, v>>}
          BY <2>4, <1>2 DEF VoteFor, VInv, TypeOK
        <6>2. QED
          BY <4>2, <4>4, <6>1
      <4>5. CASE a # self
          BY <2>4, <1>2, <4>2, <4>5, QA DEF VoteFor, VInv, TypeOK
      <4>6. QED
        BY <4>4, <4>5
    <3>1. ASSUME NEW w \in chosen,
                     v \in chosen'
          PROVE  w = v
      <4>1. w \in chosen'
        BY <3>3
      <4>2. VInv1'
        BY <1>2 DEF VInv, VInv1, VInv3
      <4>3. QED
        BY <1>2, <3>1, <4>1, <4>2,  VT1Prime DEF VInv
    <3>2. ASSUME NEW w, w \notin chosen, w \in chosen'
          PROVE  w = v
      <4>1. PICK c \in Ballot : ChosenIn(c, w)'
        BY <3>2 DEF chosen
      <4>2. PICK Q \in Quorum : \A a \in Q : <<c, w>> \in votes'[a]
        BY <4>1 DEF ChosenIn, VotedFor
      <4>3. PICK a \in Q : <<c, w>> \notin votes[a]
        BY <3>2 DEF chosen, ChosenIn, VotedFor
      <4>4. CASE a = self
        <5>1. votes'[self] = votes[self] \cup {<<b, v>>}
            BY <2>4, <1>2 DEF VoteFor, VInv, TypeOK
        <5>2. QED
          BY <4>4, <5>1, <4>2, <4>3
      <4>5. CASE a # self
        BY <2>4, <1>2, <4>2, <4>3, <4>5, QA DEF VoteFor, VInv, TypeOK
      <4>6. QED
        BY <4>4, <4>5
    <3>4. CASE chosen' = chosen
      BY <3>4 DEF C!vars
    <3>5. CASE chosen' # chosen
      <4>1. chosen \subseteq chosen'
        BY <3>3
      <4>2. PICK w \in chosen' : w \notin chosen
        BY <3>5, <4>1
      <4>3. w = v
        BY <4>2, <3>2
      <4>4. chosen' = chosen \cup {v}
        BY <3>2, <4>1, <4>3
      <4>5. chosen = {}
        BY <4>4, <3>1, <3>5
      <4>6. QED
        BY <4>4, <4>5 DEF C!Next
    <3>6. QED
      BY <3>4, <3>5
  <2>5. QED
    BY <2>2, <2>3, <2>4 DEF BallotAction
<1>3. QED
  <2>1. []VInv /\ [][Next]_vars => [][C!Next]_C!vars
\*    BY <1>2, RuleTLA2
    PROOF OMITTED
  <2>2. QED
\*    BY <1>1, <2>1, VT2 DEF Spec, C!Spec
    PROOF OMITTED
-----------------------------------------------------------------------------
(***************************************************************************)
(*                                Liveness                                 *)
(*                                                                         *)
(* We now state the liveness property required of our voting algorithm and *)
(* prove that it and the safety property imply specification LiveSpec of   *)
(* module Consensus under our refinement mapping.                          *)
(*                                                                         *)
(* We begin by stating two additional assumptions that are necessary for   *)
(* liveness.  Liveness requires that some value eventually be chosen.      *)
(* This cannot hold with an infinite set of acceptors.  More precisely,    *)
(* liveness requires the existence of a finite quorum.  (Otherwise, it     *)
(* would be impossible for all acceptors of any quorum ever to have voted, *)
(* so no value could ever be chosen.) Moreover, it is impossible to choose *)
(* a value if there are no values.  Hence, we make the following two       *)
(* assumptions.                                                            *)
(***************************************************************************)      
ASSUME AcceptorFinite == IsFiniteSet(Acceptor)

ASSUME ValueNonempty == Value # {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* We need the following simple results about sets and sets of numbers.    *)
(* The first belongs in a library of theorems about finite sets and        *)
(* cardinality.  Perhaps such a library will eventually be added to the    *)
(* FiniteSets module.                                                      *)
(***************************************************************************)
AXIOM SubsetOfFiniteSetFinite == 
        \A S, T : IsFiniteSet(T) /\ (S \subseteq T) => IsFiniteSet(S)

(***************************************************************************)
(* The next result can be proved from simple facts about finite sets and   *)
(* cardinality by induction on the cardinality of S.                       *)
(***************************************************************************)
AXIOM FiniteSetHasMax == 
        \A S \in SUBSET Int :
          IsFiniteSet(S) /\ (S # {}) => \E max \in S : \A x \in S : max >= x

(***************************************************************************)
(* The next result can be proved from the following facts about sets       *)
(*                                                                         *)
(*   - The empty set is finite.                                            *)
(*   - A singleton set is finite.                                          *)
(*   - The union of two finite sets is finite                              *)
(*                                                                         *)
(* by induction on j-i.                                                    *)
(***************************************************************************)
AXIOM IntervalFinite == \A i, j \in Int : IsFiniteSet(i..j)
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following theorem implies that it is always possible to find a      *)
(* ballot number b and a value v safe at b by choosing b large enough and  *)
(* then having a quorum of acceptors perform IncreaseMaxBal(b) actions.    *)
(* It will be used in the liveness proof.  Observe that it is for          *)
(* liveness, not safety, that invariant VInv3 is required.                 *)
(***************************************************************************)
THEOREM VT4 == TypeOK /\ VInv2 /\ VInv3  =>
                \A Q \in Quorum, b \in Ballot :
                   (\A a \in Q : (maxBal[a] >= b)) => \E v \in Value : SafeAt(b,v)
\* Checked as an invariant by TLC with 3 acceptors, 3 ballots, 2 values
<1>1. SUFFICES ASSUME TypeOK, VInv2, VInv3,
                      NEW Q \in Quorum, NEW b \in Ballot,
                      (\A a \in Q : (maxBal[a] >= b))
               PROVE  \E v \in Value : SafeAt(b, v)
  OBVIOUS
<1>2. CASE b = 0
  BY ValueNonempty, <1>1, SafeAtProp, <1>2
<1>3. SUFFICES ASSUME b # 0
               PROVE  \E v \in Value : SafeAt(b, v)
  BY <1>2
<1>4. SUFFICES \E v \in Value : 
                 \E c \in -1..(b-1) :
                   /\ (c # -1) => /\ SafeAt(c, v)
                                  /\ \A a \in Q :
                                       \A w \in Value :
                                           VotedFor(a, c, w) => (w = v)
                   /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
  <2>1. SUFFICES ASSUME NEW v \in Value,
                        <1>4!1!(v)
                 PROVE  SafeAt(b, v)
    OBVIOUS
  <2>2. SafeAtProp!(b, v)
    BY SafeAtProp
  <2>3. QED
    BY <2>1, <2>2, <1>1, <1>3
<1>5. CASE \A a \in Q, c \in 0..(b-1) : DidNotVoteIn(a, c)
  <2>1. PICK v \in Value : TRUE
    BY ValueNonempty
  <2> -1 \in -1..(b-1)
    BY SimpleArithmetic DEF Ballot
  <2>2. WITNESS v \in Value
  <2>3. WITNESS -1 \in -1..(b-1)
  <2>4. QED
    BY <1>5
<1>6. CASE \E a \in Q, c \in 0..(b-1) : ~DidNotVoteIn(a, c)
  <2>1. PICK c \in 0..(b-1) : 
               /\ \E a \in Q : ~DidNotVoteIn(a, c)
               /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
    <3> DEFINE S == {c \in 0..(b-1) : \E a \in Q : ~DidNotVoteIn(a, c)}
    <3>1. S # {}
        BY <1>6
    <3>2. PICK c \in S : \A d \in S : c >= d
      <4>2. (0 \in Int) /\ (b-1 \in Int)  /\ (\A x \in 0..(b-1) : x \in Int)
        BY <1>3, SimpleArithmetic DEF Ballot
      <4>3. (S \in SUBSET Int) 
        BY <4>2
      <4>4. IsFiniteSet(S)
        BY <4>2, IntervalFinite, SubsetOfFiniteSetFinite
      <4>5. QED
        BY <3>1,  <4>3, <4>4, FiniteSetHasMax
    <3>3. c \in 0..(b-1)
      OBVIOUS
    <3>4. \A d \in (c+1)..(b-1) : d \in 0..(b-1) /\ ~(c >= d)
      BY <3>3, SimpleArithmetic
    <3>5. \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
      BY <3>2, <3>4
    <3>6. \E a \in Q : ~DidNotVoteIn(a, c)
      BY <3>1
    <3>7. QED
      BY  <3>3, <3>5, <3>6
  <2>2. (c \in -1..(b-1)) /\ (c # -1) /\ (c \in Ballot)
    BY SimpleArithmetic DEF Ballot
  <2>3. PICK a0 \in Q : ~DidNotVoteIn(a0, c)
    BY <2>1
  <2>4. PICK v \in Value : VotedFor(a0, c, v)
    BY <2>3 DEF DidNotVoteIn
  <2>5. \A a \in Q : \A w \in Value :
           VotedFor(a, c, w) => (w = v)
    BY <2>2, <2>4, QA, <1>1 DEF VInv3
  <2>6. SafeAt(c, v)
    BY <1>1, <2>4, QA, <2>2 DEF VInv2
  <2>7. QED
    BY <2>1, <2>2, <2>5, <2>6 
    
<1>7. QED
  BY <1>5, <1>6
-------------------------------------------------------------------------------
(***************************************************************************)
(* The progress property we require of the algorithm is that a quorum of   *)
(* acceptors, by themselves, can eventually choose a value v.  This means  *)
(* that, for some quorum Q and ballot b, the acceptors `a' of Q must make  *)
(* SafeAt(b, v) true by executing IncreaseMaxBal(a, b) and then must       *)
(* execute VoteFor(a, b, v) to choose v.  In order to be able to execute   *)
(* VoteFor(a, b, v), acceptor `a' must not execute a Ballot(a, c) action   *)
(* for any c > b.                                                          *)
(*                                                                         *)
(* These considerations lead to the following liveness requirement         *)
(* LiveAssumption.  The WF condition ensures that the acceptors `a' in Q   *)
(* eventually execute the necessary BallotAction(a, b) actions if they are *)
(* enabled, and the [][...]_vars condition ensures that they never perform *)
(* BallotAction actions for higher-numbered ballots, so the necessary      *)
(* BallotAction(a, b) actions are enabled.                                 *)
(***************************************************************************)
LiveAssumption ==
  \E Q \in Quorum, b \in Ballot :
     \A self \in Q :
       /\ WF_vars(BallotAction(self, b))
       /\ [] [\A c \in Ballot : (c > b) => ~ BallotAction(self, c)]_vars
     
LiveSpec == Spec /\ LiveAssumption  
(***************************************************************************)
(* LiveAssumption is stronger than necessary.  Instead of requiring that   *)
(* an acceptor in Q never executes an action of a higher-numbered ballot   *)
(* than b, it suffices that it doesn't execute such an action until unless *)
(* it has voted in ballot b.  However, the natural liveness requirement    *)
(* for a Paxos consensus algorithm implies condition LiveAssumption.       *)
(*                                                                         *)
(* Condition LiveAssumption is a liveness property, constraining only what *)
(* eventually happens.  It is straightforward to replace "eventually       *)
(* happens" by "happens within some length of time" and convert            *)
(* LiveAssumption into a real-time condition.  We have not done that for   *)
(* three reasons:                                                          *)
(*                                                                         *)
(*  1. The real-time requirement and, we believe, the real-time reasoning  *)
(*     will be more complicated, since temporal logic was developed to     *)
(*     abstract away much of the complexity of reasoning about explicit    *)
(*     times.                                                              *)
(*                                                                         *)
(*  2. TLAPS does not yet support reasoning about real numbers.            *)
(*                                                                         *)
(*  3. Reasoning about real-time specifications consists entirely          *)
(*     of safety reasoning, which is almost entirely action reasoning.     *)
(*     We want to see how the TLA+ proof language and TLAPS do on          *)
(*     temporal logic reasoning.                                           *)
(*                                                                         *)
(*                                                                         *)
(***************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                       Some Temporal Logic Proof Rules                   *)
(*                                                                         *)
(* We now state some temporal logic proof rules that are used in the       *)
(* liveness proof.  Some version of these rules will eventually be added   *)
(* to the TLAPS module.                                                    *)
(*                                                                         *)
(* The first rule is the lattice rule.  To state it, we define             *)
(* WellFounded(S, LT) to assert that the relation LT is a well-founded     *)
(* "less-than" relation on the set S.  This means that there is no         *)
(* infinite sequence of elements of S, each of which is less than the      *)
(* previous one.  We represent a relation the way mathematicians generally *)
(* do, as a set of ordered pairs.  In this case <<s, t>> \in LT means that *)
(* s is less than t.                                                       *)
(***************************************************************************)
WellFounded(S, LT) == ~ \E f \in [Nat -> S] : 
                           \A i \in Nat : <<f[i+1], f[i]>> \in LT

(***************************************************************************)
(* We now define ProperSubsetRel(S) to be the relation on a set S such     *)
(* that <<U, V>> \in S if and only if U and V are subsets of S with U a    *)
(* proper subset of V.  We then state without proof the result that, if S  *)
(* is a finite set, then ProperSubsetRel(S) is a well-founded relation on  *)
(* S.                                                                      *)
(***************************************************************************)
ProperSubsetRel(S) == 
  {r \in (SUBSET S) \X (SUBSET S) : /\ r[1] \subseteq r[2]
                                    /\ r[1] # r[2] }     
                                                     
THEOREM SubsetWellFounded ==
           \A S : IsFiniteSet(S) => WellFounded(SUBSET S, ProperSubsetRel(S))
PROOF OMITTED

(***************************************************************************)
(* Here is our statement of the Lattice Rule, which is discussed in        *)
(*                                                                         *)
(*    AUTHOR = "Leslie Lamport",                                           *)
(*    TITLE = "The Temporal Logic of Actions",                             *)
(*    JOURNAL = toplas,                                                    *)
(*    volume = 16,                                                         *)
(*    number = 3,                                                          *)
(*    YEAR = 1994,                                                         *)
(*    month = may,                                                         *)
(*    PAGES = "872--923"                                                   *)
(***************************************************************************)
THEOREM LatticeRule ==  ASSUME NEW S, NEW LT, WellFounded(S, LT),
                               NEW TEMPORAL P(_), NEW TEMPORAL Q
                        PROVE  /\ Q \/ (\E i \in S : P(i))
                               /\ \A i \in S : 
                                     P(i) ~> (Q \/ \E j \in S : (<<j, i>> \in LT) /\ P(j))
                               => ((\E i \in S : P(i)) ~> Q)
PROOF OMITTED

(***************************************************************************)
(* Here are two more temporal-logic proof rules.  Their validity is        *)
(* obvious when you understand what they mean.  We present a proof of the  *)
(* second, mostly to show how temporal logic proofs look in TLA+.  Since   *)
(* almost all the steps are temporal formulas, we don't bother trying to   *)
(* check any of them.                                                      *)
(***************************************************************************)
THEOREM AlwaysForall ==
           ASSUME NEW CONSTANT S, NEW TEMPORAL P(_)
           PROVE  (\A s \in S : []P(s)) <=> [](\A s \in S : P(s))

LEMMA EventuallyAlwaysForall == 
        ASSUME NEW CONSTANT S, IsFiniteSet(S),
               NEW TEMPORAL P(_)
        PROVE  (\A s \in S : <>[]P(s)) => <>[](\A s \in S : P(s))
(*******
<1> DEFINE Hyp == \A s \in S : <>[]P(s)
           Q(T) == \A s \in S \ T : []P(s)
           LT  == ProperSubsetRel(S)
<1>1. Hyp => \E T \in SUBSET S : Q(T)
  <2>1. Hyp => Q(S)
  <2>2. QED
    BY <2>1
<1>2. Hyp => \A T \in SUBSET S : 
                Q(T) ~> (Q({}) \/ \E R \in SUBSET S : <<R, T>> \in LT /\ Q(R))
  <2>1 SUFFICES ASSUME NEW T \in SUBSET S
                PROVE  Hyp => 
                         (Q(T) ~> (Q({}) \/ 
                                     \E R \in SUBSET S : <<R, T>> \in LT /\ Q(R)))
    OBVIOUS
  <2>2. CASE T # {}
    <3>1. PICK s \in T : TRUE
      BY <2>2
    <3>1a. s \in S
      OBVIOUS
    <3> DEFINE R == T \ {s}
    <3>2. (<<R, T>> \in LT) /\ (S \ R = (S \ T) \cup {s})
      BY DEF ProperSubsetRel
    <3>3. Hyp => <>[]P(s)
      BY s \in S
    <3>4. Q(T) <=> []Q(T)
      BY AlwaysForall (* PTL *)
    <3>5. <>[]P(s) => [](Q(T) => <>(Q(T) /\ []P(s)))
      BY <3>4 (* PTL *)
    <3>6. Q(T) /\ []P(s) <=> Q(R)
      BY <3>2
    <3>7. Hyp => (Q(T) ~> Q(R))
      BY <3>3, <3>5, <3>6 (* PTL *)
    <3>8. QED
      BY <3>7, <3>2 (* PTL *)
  <2>3. CASE T = {}   
    OBVIOUS (* PTL, which implies A ~> A *)
  <2>4. QED
    BY <2>2, <2>3
<1>3. (\A s \in S : <>[]P(s)) => (\E T \in SUBSET S : Q(T)) ~> Q({})
  BY <1>2, SubsetWellFounded, LatticeRule 
<1>4. <> Q({})
  BY <1>1, <1>3 (* PTL *)
<1>5. QED
  <2>1. Q({}) <=> [](\A s \in S : P(s))
    BY AlwaysForall
  <2>2. QED
    BY <1>4, <2>1
*****)
PROOF OMITTED
-----------------------------------------------------------------------------
(***************************************************************************)
(* Here is our proof that LiveSpec implements the specification LiveSpec   *)
(* of module Consensus under our refinement mapping.                       *)
(***************************************************************************)
THEOREM Liveness == LiveSpec => C!LiveSpec
<1> SUFFICES ASSUME NEW Q \in Quorum, NEW b \in Ballot
             PROVE  Spec /\ LiveAssumption!(Q, b) => C!LiveSpec
\*  BY DEF LiveSpec, LiveAssumption
  PROOF OMITTED
  
<1>1. C!LiveSpec <=> C!Spec /\ ([]<><<C!Next>>_C!vars \/ []<>(chosen # {}))
\*  BY ValueNonempty, C!LiveSpecEquals (* which implies C!ValueNonempty *)
  PROOF OMITTED

<1> DEFINE LNext == \E self \in Acceptor, c \in Ballot :
                         /\ BallotAction(self, c)
                         /\ (self \in Q) => (c =< b)
                   
<1>2. Spec /\ LiveAssumption!(Q, b) => [][LNext]_vars
  <2>1. /\ TypeOK
        /\ [Next]_vars 
        /\ \A self \in Q : 
             [\A c \in Ballot : (c > b) => ~ BallotAction(self, c)]_vars
        => [LNext]_vars
    <3> SUFFICES ASSUME <2>1!1
                 PROVE  [LNext]_vars
      OBVIOUS
    <3>1. [/\ \E self \in Acceptor :
                 \E c \in Ballot : BallotAction(self, c)]_vars
      BY NextDef
    <3>2.[\A self \in Q,  c \in Ballot : 
            (c > b) => ~ BallotAction(self, c)]_vars
      OBVIOUS
    <3>3. [ /\ \E self \in Acceptor :
                 \E c \in Ballot : BallotAction(self, c)
            /\ \A self \in Q,  c \in Ballot : 
                  (c > b) => ~ BallotAction(self, c)]_vars
      BY <3>1, <3>2
    <3>4. /\ \E self \in Acceptor :
                 \E c \in Ballot : BallotAction(self, c)
          /\ \A self \in Q,  c \in Ballot : 
                  (c > b) => ~ BallotAction(self, c)
          => \E self \in Acceptor, c \in Ballot :
                /\ BallotAction(self, c)
                /\ (self \in Q) => (c =< b)
      <4> SUFFICES ASSUME <3>4!1
                   PROVE  <3>4!2
        OBVIOUS
      <4>1. PICK self \in Acceptor : \E c \in Ballot : BallotAction(self, c)
        OBVIOUS
      <4>2. PICK c \in Ballot : BallotAction(self, c)
        BY <4>1
      <4>3. (c > b) <=> ~(c =< b)
        BY SimpleArithmetic DEF Ballot
      <4>99. QED
        BY <4>2, <4>3
    <3>5. QED
      BY <3>3, <3>4 DEF LNext         
  <2>2. /\ []TypeOK 
        /\ [][Next]_vars 
        /\ \A self \in Q : 
             [][\A c \in Ballot : (c > b) => ~ BallotAction(self, c)]_vars
        => [][LNext]_vars
\*    BY <2>1 (* PTL *)
  PROOF OMITTED
  <2>3. LiveAssumption!(Q, b) => 
          \A self \in Q : 
             [][\A c \in Ballot : (c > b) => ~ BallotAction(self, c)]_vars
\*    OBVIOUS    
    PROOF OMITTED
  <2>4. QED
\*    BY <2>2, <2>3, VT2 DEF Spec
    PROOF OMITTED
  
<1> DEFINE LNInv1 == \A a \in Q : maxBal[a] =< b
           LInv1  == VInv /\ LNInv1
           
<1>3. LInv1 /\ [LNext]_vars => LInv1'
  <2>1. SUFFICES ASSUME LInv1, [LNext]_vars 
                 PROVE  LInv1'
    OBVIOUS
  <2>2. VInv'
    <3>1. [LNext]_vars => 
          [/\ \E self \in Acceptor :
                 \E c \in Ballot : BallotAction(self, c)]_vars
      OBVIOUS 
    <3>2. [Next]_vars = 
          [\E self \in Acceptor :
                 \E c \in Ballot : BallotAction(self, c)]_vars
      BY <2>1, NextDef DEF LInv1, VInv      
    <3>3. QED
      BY <2>1, <3>1, <3>2, InductiveInvariance DEF LInv1
  <2>3. LNInv1'
    <3>1. CASE vars' = vars
      BY <2>1, <3>1 DEF vars, LNInv1
    <3>2. SUFFICES ASSUME NEW self \in Acceptor, 
                          NEW c \in Ballot,
                          BallotAction(self, c),
                          (self \in Q) => (c =< b),
                          NEW a \in Q
                   PROVE  maxBal'[a] =< b
      BY <2>1, <3>1 DEF LNInv1
    <3> a \in Acceptor
      BY QA
    <3>3. CASE self = a
      <4>1. c =< b
        BY <3>2, <3>3
      <4>2. maxBal'[self] = c
        BY <3>2, <3>3, <2>1 
           DEF BallotAction, IncreaseMaxBal, VoteFor, VInv, TypeOK
      <4>3. QED
        BY <4>1, <4>2, <3>3
    <3>4. CASE self # a \* \notin Q
      <4>1. CASE IncreaseMaxBal(self, c)
        BY <4>1, <3>4, <2>1 DEF LInv1, LNInv1, IncreaseMaxBal, VInv, TypeOK
      <4>2. CASE \E v \in Value : VoteFor(self, c, v)
        BY <4>2, <3>4, <2>1 DEF LInv1, LNInv1, VoteFor, VInv, TypeOK
      <4>3. QED
        BY <3>2, <4>1, <4>2 DEF BallotAction
    <3>5. QED
      BY <3>3, <3>4                          
  <2>4. QED
    BY <2>2, <2>3 DEF LInv1

<1>4. \A a \in Q : 
          VInv /\ (maxBal[a] = b) /\ [LNext]_vars => VInv' /\ (maxBal'[a] = b)
  \* Much of this proof copied without from proof for LInv1, without
  \* checking how much of it was needed.            
  <2>1. SUFFICES ASSUME NEW a \in Q,
                        VInv, maxBal[a] = b, [LNext]_vars
                 PROVE  VInv' /\ (maxBal'[a] = b)
    OBVIOUS
  <2>2. VInv'
    <3>1. [LNext]_vars => 
          [/\ \E self \in Acceptor :
                 \E c \in Ballot : BallotAction(self, c)]_vars
      OBVIOUS 
    <3>2. [Next]_vars = 
          [\E self \in Acceptor :
                 \E c \in Ballot : BallotAction(self, c)]_vars
      BY <2>1, NextDef DEF VInv      
    <3>3. QED
      BY <2>1, <3>1, <3>2, InductiveInvariance 
  <2>3. maxBal'[a] = b
    <3>1. CASE vars' = vars
      BY <2>1, <3>1 DEF vars

    <3>2. SUFFICES ASSUME NEW self \in Acceptor, 
                          NEW c \in Ballot,
                          BallotAction(self, c),
                          (self \in Q) => (c =< b)
                   PROVE  maxBal'[a] = b
      BY <2>1, <3>1 
    <3> a \in Acceptor
      BY QA
    <3>3. CASE self = a
      <4>1. c =< b
        BY <3>2, <3>3
      <4>2. CASE IncreaseMaxBal(self, c)
        <5>1. c > b
          BY <4>2, <3>3, <2>1 DEF IncreaseMaxBal
        <5>2. ~(c > b)
          BY <4>1, SimpleArithmetic DEF Ballot
        <5>3. QED BY <5>1, <5>2
      <4>3. CASE \E v \in Value : VoteFor(self, c, v)
        <5>1. PICK v \in Value : VoteFor(self, c, v)
          BY <4>3
        <5>2. b \leq c
          BY <3>3, <5>1, <2>1 DEF VoteFor
        <5>3. b = c
          BY <4>1, <5>2, SimpleArithmetic DEF Ballot
        <5>4. QED
          BY <2>1, <5>1, <5>3 DEF VoteFor, VInv, TypeOK
      <4>4. QED
        BY <4>2, <4>3, <3>2 DEF BallotAction
    <3>4. CASE self # a \* \notin Q
      <4>1. CASE IncreaseMaxBal(self, c)
        BY <4>1, <3>4, <2>1 DEF IncreaseMaxBal, VInv, TypeOK
      <4>2. CASE \E v \in Value : VoteFor(self, c, v)
        BY <4>2, <3>4, <2>1 DEF VoteFor, VInv, TypeOK
      <4>3. QED
        BY <3>2, <4>1, <4>2 DEF BallotAction
    <3>5. QED
      BY <3>3, <3>4
  <2>99. QED
    BY <2>2, <2>3
    
<1>5. Spec /\ LiveAssumption!(Q, b) => 
         <>[](\A self \in Q : maxBal[self] = b)
  <2>1. SUFFICES ASSUME NEW self \in Q
                 PROVE  Spec /\ LiveAssumption!(Q, b) => <>[](maxBal[self] = b)
\*    BY EventuallyAlwaysForall
    PROOF OMITTED
  <2> DEFINE P ==  LInv1 /\ (maxBal[self] # b)
             QQ == LInv1 /\ (maxBal[self] = b)
             A == BallotAction(self, b)
  <2>2. [][LNext]_vars /\ WF_vars(A) => (LInv1 ~> QQ) 
    <3>1. P /\ [LNext]_vars => (P' \/ QQ')
      BY <1>3
    <3>2. P /\ <<LNext /\ A>>_vars => QQ'
      <4>1. SUFFICES ASSUME LInv1, LNext, A
                     PROVE  QQ'
        OBVIOUS
      <4>2. LInv1'
        BY <4>1, <1>3
      <4>3. CASE IncreaseMaxBal(self, b)
        <5>1. maxBal'[self] = b
          BY <4>1, <4>3, QA DEF IncreaseMaxBal, VInv, TypeOK
        <5>2. QED
          BY <4>2, <5>1
      <4>4. CASE \E v \in Value : VoteFor(self, b, v)
        <5>1. PICK v \in Value : VoteFor(self, b, v)
          BY <4>4
        <5>2. maxBal'[self] = b
          BY <4>1, <5>1, QA DEF VoteFor, VInv, TypeOK
        <5>3. QED
          BY <4>2, <5>2        
      <4>5. QED
        BY <4>1, <4>3, <4>4 DEF BallotAction
    <3>3. P => ENABLED <<A>>_vars
      <4>1. (ENABLED <<A>>_vars) = 
              \E votesp, maxBalp:
                 /\ \/ /\ b > maxBal[self]
                       /\ maxBalp = [maxBal EXCEPT ![self] = b]
                       /\ votesp = votes
                    \/ \E v \in Value :
                          /\ maxBal[self] \leq b
                          /\ DidNotVoteIn(self, b)
                          /\ \A p \in Acceptor \ {self} :
                                \A w \in Value : VotedFor(p, b, w) => (w = v)
                          /\ SafeAt(b, v)
                          /\ votesp = [votes EXCEPT ![self] = votes[self] 
                                                                \cup {<<b, v>>}]
                          /\ maxBalp = [maxBal EXCEPT ![self] = b]
                 /\ <<votesp, maxBalp>> #  <<votes, maxBal>>  
\*        BY DEF BallotAction, IncreaseMaxBal, VoteFor, vars, SafeAt, 
\*               DidNotVoteIn, VotedFor
        PROOF OMITTED
      <4>2. SUFFICES ASSUME P
                     PROVE <4>1!2
\*        BY <4>1
        PROOF OMITTED
      <4>3. SUFFICES \E votesp, maxBalp:
                        /\ /\ b > maxBal[self]
                           /\ maxBalp = [maxBal EXCEPT ![self] = b]
                           /\ votesp = votes
                        /\ <<votesp, maxBalp>> #  <<votes, maxBal>>
        OBVIOUS
      <4> WITNESS votes, [maxBal EXCEPT ![self] = b]
      <4>4. b > maxBal[self]
        <5>1. \A mbs \in Ballot \cup {-1} : mbs =< b /\ mbs # b => b > mbs
          BY SimpleArithmetic DEF Ballot
        <5>2. maxBal[self] \in Ballot \cup {-1}
          BY <4>2, QA DEF LInv1, VInv, TypeOK
        <5>3. QED
          BY <5>1, <5>2, <4>2 DEF LInv1, LNInv1
      <4>5. [maxBal EXCEPT ![self] = b][self] = b
        BY <4>2, QA DEF LInv1, VInv, TypeOK
      <4>6. b # maxBal[self]
        <5>1. \A mbs \in Ballot \cup {-1} : b > mbs => b # mbs
          BY SimpleArithmetic DEF Ballot
        <5>2. QED
          BY <4>4, <4>2, QA DEF LInv1, VInv, TypeOK
      <4>7. QED  
        BY <4>4, <4>5, <4>6     
    <3>4. QED
\*      BY <3>1, <3>2, <3>3, RuleWF1
      PROOF OMITTED
  <2>3. QQ /\ [][LNext]_vars => []QQ
    <3>1. QQ /\ [LNext]_vars => QQ'
      BY <1>3, <1>4
    <3>2. QED
\*      BY <3>1, RuleINV1
      PROOF OMITTED
  <2>4. []QQ => [](maxBal[self] = b)
    <3>1. QQ => (maxBal[self] = b)
      OBVIOUS
    <3>2. QED 
\*      OBVIOUS (* PTL *)
      PROOF OMITTED
  <2>5. QED
\*    BY <2>2, <2>3, <2>4, <1>2 (* PTL *)
    PROOF OMITTED

<1> DEFINE LNInv2 == \A a \in Q : maxBal[a] = b
           LInv2  == VInv /\ LNInv2

<1>6. LInv2 /\ [LNext]_vars => LInv2'
  <2>1. SUFFICES ASSUME VInv, \A a \in Q : maxBal[a] = b,
                        [LNext]_vars
                 PROVE  VInv' /\ (\A a \in Q : maxBal'[a] = b)
    OBVIOUS
  <2>2. VInv'
    <3>1. PICK a \in Q : maxBal[a] = b
      BY <2>1, QuorumNonEmpty
    <3>2. QED
      BY <2>1, <3>1, <1>4
  <2>3. ASSUME NEW a \in Q
        PROVE  maxBal'[a] = b
    BY <2>1, <2>3, <1>4
  <2>4. QED
    BY <2>2, <2>3

<1>7. Spec /\ LiveAssumption!(Q, b) => <>(chosen # {})
  <2> DEFINE Voted(a) == \E v \in Value : VotedFor(a, b, v)
  <2>1. LInv2 /\ (\A a \in Q : Voted(a)) => (chosen # {})
    <3>1. SUFFICES ASSUME LInv2,
                          \A a \in Q : Voted(a)
                   PROVE  chosen # {}
     OBVIOUS
    <3>2. \E v \in Value : \A a \in Q :  VotedFor(a, b, v)
      <4>1. PICK a0 \in Q : Voted(a0)
        BY <3>1, QuorumNonEmpty
      <4>2. PICK v \in Value : VotedFor(a0, b, v)
        BY <4>1
      <4>3. ASSUME NEW a \in Q
            PROVE  VotedFor(a, b, v)
        <5>1. PICK w \in Value : VotedFor(a, b, w)
          BY <3>1
        <5>2. a0 \in Acceptor /\ a \in Acceptor
          BY QA
        <5>3. w = v
          BY <4>2, <5>1, <5>2, <3>1 DEF LInv2, VInv, VInv3
        <5>4. QED
          BY <5>1, <5>3
      <4>4. QED
        BY <4>3
    <3>3. QED
      BY <3>2 DEF chosen, ChosenIn
  <2>2. Spec /\ LiveAssumption!(Q, b) => (\A a \in Q : <>[]Voted(a))
    <3>1. SUFFICES ASSUME NEW self \in Q
                   PROVE  Spec /\ LiveAssumption!(Q, b) => <>[]Voted(self)
\*      OBVIOUS
    PROOF OMITTED
    <3>2. Spec /\ LiveAssumption!(Q, b) => <>Voted(self)
      <4>1. Spec /\ LiveAssumption!(Q, b) => <>[]LInv2
        <5>1. Spec => []VInv
\*          BY VT2
          PROOF OMITTED
        <5>2. Spec /\ LiveAssumption!(Q, b) => <>[]LNInv2
\*          BY <1>5
          PROOF OMITTED
        <5>3. QED
\*          BY <5>1, <5>2 (* PTL *)
          PROOF OMITTED
      <4>2. [][LNext]_vars /\ WF_vars(BallotAction(self, b))
               => ((LInv2 /\ ~Voted(self)) ~> LInv2 /\ Voted(self))
        <5> DEFINE P == LInv2 /\ ~Voted(self)
                   QQ == LInv2 /\ Voted(self)
                   A == BallotAction(self, b)
        <5>1. P /\ [LNext]_vars => (P' \/ QQ')
          BY <1>6                     
        <5>2. P /\ <<LNext /\ A>>_vars => QQ'
          <6>1. SUFFICES ASSUME P,
                                LNext,
                                A
                         PROVE QQ'
            OBVIOUS
          <6>2. CASE \E v \in Value : VoteFor(self, b, v)
            <7>2. PICK v \in Value : VoteFor(self, b, v)
              BY <6>2
            <7>3. LInv2'
              BY <5>1, <6>1
            <7>4. Voted(self)'
              BY <6>1, <7>2, QA DEF VoteFor, Voted, VotedFor, LInv2, VInv, TypeOK
            <7>5. QED
              BY <7>3, <7>4
          <6>3. CASE IncreaseMaxBal(self, b)
            <7>1. ~ (b > b)
              BY SimpleArithmetic DEF Ballot 
            <7>2. QED
              BY <7>1, <6>1, <6>3 DEF IncreaseMaxBal              
          <6>4. QED
            BY <6>1, <6>2, <6>3 DEF BallotAction
        <5>3. P => ENABLED <<A>>_vars
          <6>1. SUFFICES ASSUME P
                         PROVE  ENABLED <<A>>_vars
\*            OBVIOUS
            PROOF OMITTED
          <6>2. (ENABLED <<A>>_vars) = 
                  \E votesp, maxBalp :
                     /\ \/ /\ b > maxBal[self]
                           /\ maxBalp = [maxBal EXCEPT ![self] = b]
                           /\ votesp = votes
                        \/ \E v \in Value :
                              /\ maxBal[self] \leq b
                              /\ DidNotVoteIn(self, b)
                              /\ \A p \in Acceptor \ {self} :
                                  \A w \in Value : VotedFor(p, b, w) => (w = v)
                              /\ SafeAt(b, v)
                              /\ votesp = [votes EXCEPT ![self] = votes[self] 
                                                                \cup {<<b, v>>}]
                              /\ maxBalp = [maxBal EXCEPT ![self] = b]
                     /\ <<votesp, maxBalp>> #  <<votes, maxBal>>  
\*        BY DEF BallotAction, IncreaseMaxBal, VoteFor, vars, SafeAt, 
\*               DidNotVoteIn, VotedFor
        PROOF OMITTED        
          <6> SUFFICES <6>2!2
\*            BY <6>2
            PROOF OMITTED
          <6> SUFFICES
                  \E votesp, maxBalp:
                     /\ \E v \in Value :
                           /\ maxBal[self] \leq b
                           /\ DidNotVoteIn(self, b)
                           /\ \A p \in Acceptor \ {self} :
                                \A w \in Value : VotedFor(p, b, w) => (w = v)
                           /\ SafeAt(b, v)
                           /\ votesp = [votes EXCEPT ![self] = votes[self] 
                                                                \cup {<<b, v>>}]
                           /\ maxBalp = [maxBal EXCEPT ![self] = b]
                     /\ <<votesp, maxBalp>> #  <<votes, maxBal>>  
            OBVIOUS
          <6> DEFINE someVoted == \E p \in Acceptor \ {self} :
                                   \E w \in Value : VotedFor(p, b, w)
                     vp == CHOOSE p \in Acceptor \ {self} :
                                   \E w \in Value : VotedFor(p, b, w)
                     vpval == CHOOSE w \in Value : VotedFor(vp, b, w)
          <6>3. someVoted => /\ vp \in Acceptor
                             /\ vpval \in Value
                             /\ VotedFor(vp, b, vpval)
            OBVIOUS
          <6> DEFINE v == IF someVoted THEN vpval
                                       ELSE CHOOSE v \in Value : SafeAt(b, v)
          <6>4. (v \in Value) /\ SafeAt(b, v)
            <7>1. CASE someVoted
              BY <6>3, <6>1, <7>1 DEF LInv2, VInv, VInv2
            <7>2. CASE ~ someVoted
              <8>1. b >= b
                BY SimpleArithmetic DEF Ballot
              <8>2. QED
                BY <6>1, <7>2, <8>1, VT4 DEF LInv2, VInv
            <7>3. QED
              BY <7>1, <7>2
          <6> DEFINE votesp == [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
                     maxBalp == [maxBal EXCEPT ![self] = b]
          <6> WITNESS votesp, maxBalp
          <6> SUFFICES /\ maxBal[self] \leq b
                       /\ DidNotVoteIn(self, b)
                       /\ \A p \in Acceptor \ {self} :
                                \A w \in Value : VotedFor(p, b, w) => (w = v)
                       /\ votesp # votes
            BY <6>4
          <6>5. maxBal[self] \leq b
            <7>1. b \leq b
              BY SimpleArithmetic DEF Ballot
            <7>2. QED
              BY <7>1, <6>1
          <6>6. DidNotVoteIn(self, b)
            BY <6>1 DEF Voted, DidNotVoteIn
          <6>7. ASSUME NEW p \in Acceptor \ {self},
                       NEW w \in Value, 
                       VotedFor(p, b, w) 
                PROVE  w = v
            BY <6>7, <6>3, <6>1 DEF LInv2, VInv, VInv3
          <6>8. votesp # votes
            <7>1. votesp[self] = votes[self] \cup {<<b, v>>}
              BY <6>1, QA DEF LInv2, VInv, TypeOK
            <7>2. <<b, v>> \in votesp[self]
              BY <7>1
            <7>3. \A w \in Value : <<b, w>> \notin votes[self]
              BY <6>6 DEF DidNotVoteIn, VotedFor
            <7>4. QED 
              BY <7>2, <7>3, <6>4
          <6>9. QED
            BY <6>5, <6>6, <6>7, <6>8
        <5>4. QED
\*          BY <5>1, <5>2, <5>3, RuleWF1
          PROOF OMITTED
      <4>3. []LInv2 /\ ((LInv2 /\ ~Voted(self)) ~> LInv2 /\ Voted(self))
              => <>Voted(self)
\*        OBVIOUS (* PTL *)
          PROOF OMITTED
      <4>4. QED
\*        BY <1>2, <4>1, <4>2, <4>3  (* And Def LiveAssumption *)
          PROOF OMITTED
    <3>3. Spec => [](Voted(self) => []Voted(self))
      <4>1. (VInv /\ Voted(self)) /\ [Next]_vars => (VInv /\ Voted(self))'
        <5> SUFFICES ASSUME VInv, Voted(self), [Next]_vars
                     PROVE  VInv' /\ Voted(self)'
          OBVIOUS
        <5>1. VInv'
          BY InductiveInvariance
        <5>2. Voted(self)'
          <6> CASE vars' = vars
            BY DEF vars, Voted, VotedFor
          <6> CASE Next
            <7>1. \E a \in Acceptor :
                    \E c \in Ballot : BallotAction(a, c)
              BY NextDef DEF VInv
            <7>2. PICK a \in Acceptor, c \in Ballot : BallotAction(a, c)
              BY <7>1
            <7>3. CASE IncreaseMaxBal(a, c)
              BY <7>3 DEF IncreaseMaxBal, Voted, VotedFor
            <7>4. CASE \E v \in Value : VoteFor(a, c, v)
              <8>1. PICK v \in Value : VoteFor(a, c, v)
                BY <7>4
              <8>2. votes' = [votes EXCEPT ![a] = votes[a] \cup {<<c, v>>}]
                BY <8>1 DEF VoteFor
              <8>3. CASE a = self
                <9>1. votes'[self] = votes[self] \cup {<<c, v>>}
                  BY <8>2, <8>3 DEF VInv, TypeOK
                <9>2. PICK w \in Value : <<b, w>> \in votes[self]
                  BY DEF Voted, VotedFor
                <9>3. <<b, w>> \in votes'[self]
                  BY <9>1, <9>2
                <9>4. QED
                  BY <9>3 DEF Voted, VotedFor
              <8>4. CASE a # self
                <9>1. votes'[self] = votes[self]
                  BY <8>2, <8>4, QA DEF VInv, TypeOK
                <9>2. QED
                  BY <9>1 DEF Voted, VotedFor
              <8>5. QED
                BY <8>3, <8>4
            <7>5. QED
              BY <7>2, <7>3, <7>4 DEF BallotAction
          <6> QED
            OBVIOUS
        <5>3. QED
          BY <5>1, <5>2
        
      <4>2. (VInv /\ Voted(self)) /\ [][Next]_vars => [](VInv /\ Voted(self))
\*        BY <4>1, RuleINV1
        PROOF OMITTED
      <4>3. QED
        <5>1. VInv /\ [][Next]_vars => (Voted(self) => []Voted(self))
\*          BY <4>2 (* PTL *)
          PROOF OMITTED
        <5>2. []VInv /\ [][Next]_vars => [](Voted(self) => []Voted(self))
\*          BY <5>1 (* PTL *)
          PROOF OMITTED
        <5>3. QED
\*          BY <5>2, VT2 DEF Spec
          PROOF OMITTED
    <3>4. QED
\*      BY <3>2, <3>3 (* PTL *) 
          PROOF OMITTED
  <2>3. (\A a \in Q : <> []Voted(a)) => <> [](\A a \in Q : Voted(a))
    <3>1. IsFiniteSet(Q)
      BY AcceptorFinite, QA, SubsetOfFiniteSetFinite
    <3>2. QED
\*      BY <3>1, EventuallyAlwaysForall
      PROOF OMITTED
  <2>4. <> [](\A a \in Q : Voted(a)) => <> (\A a \in Q : Voted(a))
\*    OBVIOUS (* PTL *)
    PROOF OMITTED
  <2>5. <>(\A a \in Q : Voted(a))=> <>(chosen # {})
\*    BY <2>1 (* PTL *)
    PROOF OMITTED
  <2>6. QED
\*    BY <2>2, <2>3, <2>4, <2>5
    PROOF OMITTED

<1>8. []VInv /\ [][Next]_vars /\ <>(chosen # {}) => <>[](chosen # {})
  <2>1. []VInv /\ (chosen # {}) /\  [][Next]_vars  => [](chosen # {})
    <3>1. (chosen # {}) /\ [Next /\ VInv /\ VInv']_vars => (chosen' # {})
      <4> SUFFICES ASSUME chosen # {}, [Next /\ VInv /\ VInv']_vars
                   PROVE  chosen' # {}
        OBVIOUS
      <4> CASE vars' = vars
        BY DEF vars, chosen, ChosenIn, VotedFor
      <4> CASE Next /\ VInv /\ VInv'
        <5>1. PICK self \in Acceptor, c \in Ballot : BallotAction(self, c)
          BY NextDef DEF VInv
        <5>2. CASE IncreaseMaxBal(self, c)
          BY <5>2 DEF IncreaseMaxBal, chosen, ChosenIn, VotedFor
        <5>3. CASE \E v \in Value : VoteFor(self, c, v)
          <6>1. PICK v \in Value : VoteFor(self, c, v)
            BY <5>3
          <6>2. votes' = [votes EXCEPT ![self] = votes[self] \cup {<<c, v>>}]
            BY <6>1 DEF VoteFor, VInv, TypeOK
          <6>3. \A a \in Acceptor : votes[a] \subseteq votes'[a]
            <7> SUFFICES ASSUME NEW a \in Acceptor
                         PROVE  votes[a] \subseteq votes'[a]
              OBVIOUS
            <7> QED
              BY <6>2 DEF VInv, TypeOK 
          <6>4. \A a \in Acceptor, d \in Ballot, w \in Value : 
                    VotedFor(a, d, w) => VotedFor(a, d, w)'
            BY <6>3 DEF VotedFor
          <6>5. ASSUME NEW d \in Ballot, NEW w \in Value, ChosenIn(d, w)
                PROVE  ChosenIn(d, w)'
            <7>1. PICK QQ \in Quorum : \A a \in QQ : VotedFor(a, d, w)
              BY <6>5 DEF ChosenIn
            <7>2. \A a \in QQ : VotedFor(a, d, w)'
              BY QA, <6>4, <7>1
            <7>3. QED
              BY <7>2 DEF ChosenIn
          <6>6. QED
            BY <6>5 DEF  chosen
        <5>4. QED
          BY <5>1, <5>2, <5>3 DEF BallotAction
      <4> QED
        OBVIOUS
    <3>2. (chosen # {}) /\ [][Next /\ VInv /\ VInv']_vars => [](chosen # {})
\*      BY <3>1, RuleINV1
      PROOF OMITTED
    <3>3. []VInv /\ [][Next]_vars => [][Next /\ VInv /\ VInv']_vars
\*      BY RuleINV2
      PROOF OMITTED
    <3>4. QED
\*      BY <3>2, <3>3
    PROOF OMITTED
  <2>2. QED
\*    BY <2>1 \* and PTL
    PROOF OMITTED

<1>9 Spec /\ LiveAssumption!(Q, b) => <>[](chosen # {})
  <2>1. Spec => []VInv /\ [][Next]_vars
\*    BY VT2 DEF Spec
    PROOF OMITTED
  <2>2. Spec /\ LiveAssumption!(Q, b) => 
           []VInv /\ [][Next]_vars /\ <>(chosen # {})
\*    BY <2>1, <1>7
    PROOF OMITTED
  <2>3. QED
\*   BY <1>8, <2>2
    PROOF OMITTED

<1>10. QED
  <2>1. Spec /\ LiveAssumption!(Q, b) => C!Spec /\ <>[](chosen # {})
\*    BY VT3, <1>9
    PROOF OMITTED
  <2>2. Spec /\ LiveAssumption!(Q, b) => C!Spec /\ []<>(chosen # {})
\*    BY <2>1 (* And PTL (<>[] => []<>) *)
    PROOF OMITTED
  <2>3. QED
\*    BY <2>2, <1>1 
    PROOF OMITTED 

===============================================================================
\* Modification History
\* Last modified Wed Feb 16 15:20:49 PST 2011 by lamport


