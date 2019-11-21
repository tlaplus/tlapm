------------------------------- MODULE Voting -------------------------------

EXTENDS Sets

CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
\*THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
\*BY ONLY QuorumAssumption

Ballot == Nat

VARIABLE votes, maxBal

VotedFor(a, b, v) == <<b, v>> \in votes[a]

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

ShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : maxBal[a] \geq b
  /\ \E c \in -1..(b-1) :
      /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
      /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)

Init == /\ votes = [a \in Acceptor |-> {}]
        /\ maxBal = [a \in Acceptor |-> -1]


IncreaseMaxBal(a, b) ==
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]
  /\ UNCHANGED votes


VoteFor(a, b, v) ==
    /\ maxBal[a] <= b
    /\ \A vt \in votes[a] : vt[1] # b
    /\ \A c \in Acceptor \ {a} :
         \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]


Next ==
 \E a \in Acceptor, b \in Ballot :
    \/ IncreaseMaxBal(a, b)
    \/ \E v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_<<votes, maxBal>>

ChosenAt(b, v) == \E Q \in Quorum :
                    \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

---------------------------------------------------------------------------


CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)

NoneOtherChoosableAt(b, v) ==
   \E Q \in Quorum :
     \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)

SafeAt(b, v) == \A c \in 0..(b-1) :
                   NoneOtherChoosableAt(c, v)

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

VotesSafe == \A a \in Acceptor, b \in Ballot, v \in Value :
                 VotedFor(a, b, v) => SafeAt(b, v)

OneVote == \A a \in Acceptor, b \in Ballot, v, w \in Value :
              VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)
OneValuePerBallot ==
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
       VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

Inv == TypeOK /\ VotesSafe /\ OneValuePerBallot

-----------------------------------------------------------------------------

THEOREM AllSafeAtZero == \A v \in Value : SafeAt(0, v)
  BY SMT DEF Ballot, SafeAt

THEOREM ChoosableThm ==
          \A b \in Ballot, v \in Value :
             ChosenAt(b, v) => NoneOtherChoosableAt(b, v)
  BY DEF ChosenAt, NoneOtherChoosableAt

THEOREM OneVoteThm == OneValuePerBallot => OneVote
  BY DEF OneValuePerBallot, OneVote

THEOREM VotesSafeImpliesConsistency ==
   ASSUME VotesSafe, OneVote, chosen # {}
   PROVE  \E v \in Value : chosen = {v}
<1>2. PICK v \in Value : v \in chosen
  BY DEF chosen
<1>3. SUFFICES ASSUME NEW w \in chosen
               PROVE  w = v
  BY <1>2, <1>3
<1>7. ASSUME NEW b1 \in Ballot, NEW b2 \in Ballot, b1 < b2,
             NEW v1 \in Value, NEW v2 \in Value,
             ChosenAt(b1, v1) /\ ChosenAt(b2, v2)
      PROVE  v1 = v2
  <2>1. SafeAt(b2, v2)
    BY <1>7, QuorumAssumption, SMT DEF ChosenAt, VotesSafe
  <2>8. QED
    BY <1>7, <2>1, QuorumAssumption, Z3
    DEF CannotVoteAt, DidNotVoteAt, OneVote, ChosenAt, NoneOtherChoosableAt, Ballot, SafeAt
<1>10. QED
  BY QuorumAssumption, <1>2, <1>3, <1>7, Z3 
  DEF Ballot, ChosenAt, OneVote, chosen

THEOREM ShowsSafety ==
          TypeOK /\ VotesSafe /\ OneValuePerBallot =>
             \A Q \in Quorum, b \in Ballot, v \in Value :
               ShowsSafeAt(Q, b, v) => SafeAt(b, v)
  BY QuorumAssumption, Z3
  DEFS Ballot, TypeOK, VotesSafe, OneValuePerBallot, SafeAt, 
    ShowsSafeAt, CannotVoteAt, NoneOtherChoosableAt, DidNotVoteAt

-----------------------------------------------------------------------------

THEOREM Invariance == Spec => []Inv
<1>1. Init => Inv
  BY SMT DEF Init, Inv, VotesSafe, VotedFor, TypeOK, VotesSafe, OneValuePerBallot
<1>2. ASSUME Inv, [Next]_<<votes, maxBal>>
      PROVE Inv'
  <2> USE DEF Inv, Ballot, VotedFor, VoteFor
  <2>1. CASE UNCHANGED <<votes, maxBal>>
    BY <1>2, <2>1, IsaM("auto") 
    DEFS IncreaseMaxBal, ShowsSafeAt,
         DidNotVoteAt, TypeOK, VotesSafe, OneValuePerBallot,
         SafeAt, NoneOtherChoosableAt, CannotVoteAt
  <2>2. CASE Next
  <2>3. QED
    BY <2>1, <2>2, <1>2, SMT
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

----------------------------------------------------------------------------

C == INSTANCE Consensus

THEOREM Spec /\ Inv => C!Spec
<1>1. Init => C!Init
  BY QuorumAssumption, SetExtensionality, IsaM("force")
  DEF Init, C!Init, chosen, ChosenAt, VotedFor
<1>2. Next /\ Inv => C!Next \/ UNCHANGED chosen
  <2>1 SUFFICES ASSUME Next, Inv PROVE C!Next \/ UNCHANGED chosen 
    BY <2>1
  <2>2. chosen \subseteq chosen'
    BY <2>1, QuorumAssumption, Z3   \* SMTT(10) fails
    DEF Next, Inv, TypeOK, IncreaseMaxBal, chosen, ChosenAt, VotedFor, Ballot, VoteFor
  <2>3. chosen' = {} \/ \E v \in Value : chosen' = {v}
    <3>1. PICK a \in Acceptor, b \in Ballot :
             \/ IncreaseMaxBal(a, b)
             \/ \E v \in Value : VoteFor(a, b, v)
      BY <2>1 DEF Next
    <3>2. CASE IncreaseMaxBal(a, b)
    <3>3. CASE \E v \in Value : VoteFor(a, b, v)
    <3>q. QED
      BY <3>1, <3>2, <3>3, SMT
  <2>q. QED
    BY <2>1, <2>2, <2>3, OneVoteThm, VotesSafeImpliesConsistency, SetExtensionality, SMT
    DEF Inv, C!Next
<1>3. QED
  PROOF OMITTED

=============================================================================
