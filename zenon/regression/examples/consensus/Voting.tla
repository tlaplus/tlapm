------------------------------- MODULE Voting -------------------------------

EXTENDS Integers, Sets

CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
BY ONLY QuorumAssumption

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
ASSUME auto == TRUE (*{by (isabelle "auto")}*)
-----------------------------------------------------------------------------

THEOREM AllSafeAtZero == \A v \in Value : SafeAt(0, v)
<1>1. /\ 0 \in Ballot
      /\ \A n \in 0 .. (0-1) : FALSE
  BY DEF Ballot (*{ by (cooper) }*)
<1>2. QED
  BY <1>1 DEF SafeAt

THEOREM ChoosableThm ==
          \A b \in Ballot, v \in Value :
             ChosenAt(b, v) => NoneOtherChoosableAt(b, v)
BY DEF ChosenAt, NoneOtherChoosableAt

THEOREM OneVoteThm == OneValuePerBallot => OneVote
BY DEF OneValuePerBallot, OneVote

THEOREM VotesSafeImpliesConsistency ==
          /\ TypeOK
          /\ VotesSafe
          /\ OneVote
          => \/ chosen = {}
             \/ \E v \in Value : chosen = {v}
<1>1. SUFFICES ASSUME TypeOK, VotesSafe, OneVote, chosen # {}
               PROVE  \E v \in Value : chosen = {v}
BY <1>1
<1>2. PICK v \in Value : v \in chosen
BY <1>1 DEF chosen
<1>3. SUFFICES ASSUME NEW w \in Value, w \in chosen
               PROVE  w = v
BY <1>2, <1>3 DEF chosen
<1>4. PICK bv, bw \in Ballot : ChosenAt(bv, v) /\ ChosenAt(bw, w)
BY <1>2, <1>3 DEF chosen
<1>6. CASE bv = bw
  <2>0. PICK Qv, Qw \in Quorum : /\ \A a \in Qv : VotedFor(a, bv, v)
                                 /\ \A a \in Qw : VotedFor(a, bw, w)
 BY <1>4 DEF ChosenAt
  <2>1. PICK a : a \in Qv \cap Qw
    BY QuorumAssumption
  <2>2. a \in Acceptor
    BY <2>1, QuorumAssumption
  <2>3. VotedFor(a, bv, v) /\ VotedFor(a, bv, w)
    BY <2>0, <2>1, <1>6
  <2>4. QED
    BY <2>2, <2>3, <1>1 DEF OneVote
<1>7. ASSUME NEW b1 \in Ballot, NEW b2 \in Ballot, b1 < b2,
             NEW v1 \in Value, NEW v2 \in Value,
             ChosenAt(b1, v1) /\ ChosenAt(b2, v2)
      PROVE  v1 = v2
  <2>1. SafeAt(b2, v2)
    <3>1. PICK Q2 \in Quorum : \A a \in Q2 : VotedFor(a, b2, v2)
      BY <1>7 DEF ChosenAt
    <3>2. PICK a : a \in Q2
        BY <3>1, QuorumNonEmpty
    <3>3. a \in Acceptor
      BY <3>2, QuorumAssumption
    <3>4. QED
      BY <3>1, <3>3, <1>1, <3>2 DEF VotesSafe
  <2>2. NoneOtherChoosableAt(b1, v2)
    <3>1. b1 \in 0..(b2-1)
      <4>1. \A bb1, bb2 \in Ballot : bb1 < bb2 => bb1 \in 0..(bb2-1)
        BY DEF Ballot (*{ by (cooper) }*)
      <4>2. QED
        BY <4>1, <1>7
    <3>2. QED
      BY ONLY <2>1, <3>1 DEF SafeAt
  <2>3. PICK Q2 \in Quorum :
          \A a \in Q2 : VotedFor(a, b1, v2) \/  CannotVoteAt(a, b1)
    BY <2>2 DEF NoneOtherChoosableAt
  <2>4. PICK Q1 \in Quorum : \A a \in Q1 : VotedFor(a, b1, v1)
    BY <1>7 DEF ChosenAt
  <2>5. PICK a : a \in Q1 \cap Q2
    BY <2>3, <2>4, QuorumAssumption
  <2>6. a \in Acceptor
    BY <2>5, QuorumAssumption
  <2>7. /\ VotedFor(a, b1, v1)
        /\ VotedFor(a, b1, v2) \/  CannotVoteAt(a, b1)
    BY <2>3, <2>4, <2>5
  <2>8. QED
    BY <2>6, <2>7, <1>1 DEF CannotVoteAt, DidNotVoteAt, OneVote
<1>8. CASE bv < bw
BY <1>4, <1>7, <1>8
<1>9. CASE bw < bv
BY <1>4, <1>7, <1>9
<1>10. QED
 <2>1. \A b1, b2 \in Ballot : b1=b2 \/ b1 < b2 \/ b2 <  b1
   BY DEF Ballot (*{ by (cooper) }*)
 <2>2. QED
   BY <1>6, <1>8, <1>9, <2>1

THEOREM ShowsSafety ==
          TypeOK /\ VotesSafe /\ OneValuePerBallot =>
             \A Q \in Quorum, b \in Ballot, v \in Value :
               ShowsSafeAt(Q, b, v) => SafeAt(b, v)

<1>1. SUFFICES ASSUME TypeOK, VotesSafe, OneValuePerBallot,
                      NEW Q \in Quorum, NEW b \in Ballot, NEW v \in Value,
                      ShowsSafeAt(Q, b, v),
                      NEW e \in 0..(b-1)
               PROVE  NoneOtherChoosableAt(e, v)
 BY <1>1 DEF SafeAt
<1>2. \A a \in Q : maxBal[a] \geq b
BY <1>1 DEF ShowsSafeAt
<1>3. PICK c \in -1..(b-1) :
         /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
         /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
BY <1>1 DEF ShowsSafeAt
<1>4. CASE e \geq c+1
 <2>1. e \in (c+1)..(b-1)
   BY <1>4, <1>1 DEF Ballot (*{ by (cooper) }*)
 <2>2. \A a \in Q : DidNotVoteAt(a, e)
   BY <1>3, <2>1
 <2>3. \A a \in Q : maxBal[a] > e
   <3>1. \A mb \in Ballot \cup {-1} : (mb \geq b) => (mb > e)
     BY DEF Ballot (*{ by (cooper) }*)
   <3>2. \A a \in Q : maxBal[a] \in Ballot \cup {-1}
     <4>1. \A a \in Q : a \in Acceptor
       BY QuorumAssumption
     <4>2. QED
     BY <4>1, <1>1 DEF TypeOK
   <3>3. QED
     BY <3>1, <3>2, <1>2
 <2>4. \A a \in Q : CannotVoteAt(a, e)
  BY <2>2, <2>3 DEF CannotVoteAt
 <2>5. QED
   BY <2>4 DEF NoneOtherChoosableAt
<1>5. CASE e < c+1
  <2>1. c # -1
    BY <1>1, <1>5 DEF Ballot (*{ by (cooper) }*)
  <2>2. \E a \in Acceptor : VotedFor(a, c, v)
    <3>1. \E a \in Q : VotedFor(a, c, v)
      BY <2>1, <1>3
    <3>2. QED
      BY <3>1, QuorumAssumption
  <2>3. c \in Ballot
    BY <2>1 DEF Ballot (*{ by (cooper) }*)
  <2>4. SafeAt(c, v)
    BY <2>2, <2>3, <1>1 DEF VotesSafe
  <2>5. CASE e = c
    <3>1. \A a \in Q : \/ \E vv \in Value : VotedFor(a, c, vv)
                       \/ DidNotVoteAt(a, c)
      BY DEF DidNotVoteAt
    <3>2. \A a \in Acceptor :
             \A vv \in Value : VotedFor(a, c, vv) => vv = v
      <4>1. SUFFICES ASSUME NEW a \in Acceptor,
                            NEW vv \in Value,
                            VotedFor(a, c, vv)
                     PROVE vv = v
        BY <4>1
      <4>2. PICK aa \in Acceptor : VotedFor(aa, c, v)
        BY <2>2
      <4>3. QED
        <5>0. \A a2 \in Acceptor : \A bb \in Ballot, v1, v2 \in Value :
                   VotedFor(a, bb, v1) /\ VotedFor(a2, bb, v2) => (v1 = v2)
          BY ONLY OneValuePerBallot, a \in Acceptor
             DEF OneValuePerBallot
        <5>1. \A bb \in Ballot, v1, v2 \in Value :
                   VotedFor(a, bb, v1) /\ VotedFor(aa, bb, v2) => (v1 = v2)
          BY <5>0
        <5>2. \A v1, v2 \in Value :
                   VotedFor(a, c, v1) /\ VotedFor(aa, c, v2) => (v1 = v2)
          BY <2>3, <5>1
        <5>3. QED
          BY <5>2, <4>2, <4>1

 \*
 \*

    <3>3. \A a \in Q : VotedFor(a, c, v) \/ DidNotVoteAt(a, c)
      <4>1. SUFFICES ASSUME NEW a \in Q, ~ DidNotVoteAt(a, c)
                     PROVE  VotedFor(a, c, v)
        BY <4>1
      <4>2. \A vv \in Value : VotedFor(a, c, vv) => vv = v
        BY <3>2, QuorumAssumption
      <4>3. PICK vv \in Value : VotedFor(a, c, vv)
        BY <3>1, <4>1
      <4>4. vv = v
        BY <4>2, <4>3
      <4>5. QED
        BY <4>4, <4>1, <4>3
    <3>4. \A a \in Q : maxBal[a] > c
     <4>1. SUFFICES ASSUME NEW a \in Q
                    PROVE  maxBal[a] > c
       BY <4>1
     <4>2. a \in Acceptor
       BY QuorumAssumption
     <4>3. maxBal[a] \in Ballot \cup {-1}
       BY <4>2, <1>1 DEF TypeOK
     <4>4. \A mb \in Ballot \cup {-1} : mb \geq b => mb > c
       OBVIOUS (*{ by (cooper) }*)
     <4>5. maxBal[a] \geq b
       BY <1>2
     <4>6. QED
       BY <4>3, <4>4, <4>5
    <3>5. \A a \in Q : VotedFor(a, c, v) \/ CannotVoteAt(a, c)
      BY <3>3, <3>4 DEF CannotVoteAt
    <3>6. QED
      BY <3>5, <2>5 DEF NoneOtherChoosableAt
  <2>6. CASE e \in 0..(c-1)
    <3>1. c \in Ballot
      BY DEF Ballot (*{ by (cooper) }*)
    <3>2. SafeAt(c, v)
      BY <2>2, <3>1 DEF VotesSafe
    <3>3. QED
      BY <3>2, <2>6 DEF SafeAt
  <2>7. QED
    <3>1. (e = c) \/ (e \in 0..(c-1))
      BY <2>1, <1>5 (*{ by (cooper) }*)
    <3>3. QED
      BY <2>5, <2>6, <3>1
<1>6. QED
  <2>1. \A bb \in Ballot :
           e \in 0..(bb-1) /\ c \in -1..(bb-1) => (e \geq c+1) \/ (e < c+1)
    OBVIOUS (*{ by (cooper) }*)
  <2>2. QED
   BY <1>4, <1>5, <2>1

-----------------------------------------------------------------------------
THEOREM Invariance == Spec => []Inv
<1>1. ASSUME Init
      PROVE  Inv
  BY <1>1 DEF Init, Inv, VotesSafe, VotedFor, TypeOK, VotesSafe,
              OneValuePerBallot
<1>2. ASSUME Inv, [Next]_<<votes, maxBal>>
      PROVE Inv'
  <2> USE <1>2 DEF Inv, Ballot
  <2>1. CASE UNCHANGED <<votes, maxBal>>
    BY <2>1 DEF Next, IncreaseMaxBal, VoteFor, ShowsSafeAt,
           VotedFor, DidNotVoteAt, TypeOK, VotesSafe, OneValuePerBallot,
           SafeAt, NoneOtherChoosableAt, CannotVoteAt, Ballot
           (*{by (isabelle "auto")}*)
  <2>2. CASE Next
    <3>1. ASSUME NEW a \in Acceptor, NEW b \in Ballot, IncreaseMaxBal(a, b)
          PROVE  Inv'
      <4> USE <3>1 DEF IncreaseMaxBal
      <4>a. \A Q \in Quorum : \A aa \in Q, bb \in Ballot, vv \in Value :
               VotedFor(aa, bb, vv)' <=> VotedFor(aa, bb, vv)
        BY DEF VotedFor
      <4>b. \A aa \in Acceptor, bb \in Ballot, vv \in Value :
               VotedFor(aa, bb, vv)' <=> VotedFor(aa, bb, vv)
        BY DEF VotedFor
      <4>1. TypeOK'
        BY <2>2 DEF TypeOK
      <4>2. VotesSafe'
        <5>1. VotesSafe OBVIOUS
        <5>2. \A b2 \in Ballot, v \in Value : SafeAt(b2, v) => SafeAt(b2, v)'
          <6>2. TAKE bb \in Ballot, v \in Value
          <6>3. HAVE SafeAt(bb, v)
          <6>. USE <6>3 DEF SafeAt, NoneOtherChoosableAt
          <6>3b. TAKE c \in 0 .. bb - 1
          <6>3a. c \in Ballot
            BY DEF Ballot (*{ by (cooper) }*)
          <6>4. PICK Q \in Quorum : \A a2 \in Q : VotedFor(a2, c, v) \/ CannotVoteAt(a2, c) OBVIOUS
          <6>5. WITNESS Q \in Quorum
          <6>6. TAKE aa \in Q
          <6>7. CASE VotedFor(aa, c, v)
            BY <4>a, <6>3a, <6>7
          <6>8. CASE CannotVoteAt(aa, c)
            <7>1. USE <6>8 DEF CannotVoteAt, DidNotVoteAt
            <7>2. maxBal'[aa] > c
              <8>. USE DEF TypeOK
              <8>1. CASE aa = a
                <9> USE <8>1
                <9>1. maxBal'[aa] = b OBVIOUS
                <9>2. b > maxBal[aa] OBVIOUS (* zenon fails *)
                <9>3. maxBal[aa] > c OBVIOUS
                <9>4. maxBal[aa] \in Ballot
                  <10>1. \A mb \in Ballot \cup {-1} : mb > c => mb \in Ballot
                    BY <6>3a (*{ by (cooper) }*)
                  <10>2. QED
                    BY ONLY <6>6, Q \in Quorum, QuorumAssumption, <9>3, <10>1, TypeOK
                <9>5. \A x, y, z \in Ballot : (x > y) => ((y > z) => (x > z))
                  OBVIOUS (*{ by (cooper) }*)
                <9>6. QED BY ONLY b \in Ballot, <6>3a, <9>1, <9>2, <9>3, <9>4, <9>5, TypeOK
              <8>2. CASE aa # a
                <9>0. /\ aa \in DOMAIN maxBal
                      /\ a \in DOMAIN maxBal
                  BY ONLY TypeOK, a \in Acceptor, aa \in Q, Q \in Quorum, QuorumAssumption
                <9>1. maxBal'[aa] = maxBal[aa]
                  BY ONLY aa # a, <9>0, IncreaseMaxBal(a, b)
                <9>2. maxBal[aa] > c
                  OBVIOUS
                <9>3. QED BY ONLY <9>1, <9>2
              <8>3. QED BY ONLY <8>1, <8>2
            <7>. QED BY ONLY Q \in Quorum, aa \in Q, <6>3a, v \in Value, <6>8, <4>a, <6>3a, <7>2
          <6>99. QED BY <6>7, <6>8, <6>4
        <5>3. QED
          BY ONLY <4>b, <5>1, <5>2 DEF VotesSafe, Ballot
        (* <5>. QED *)
      <4>3. OneValuePerBallot'
        <5>1. OneValuePerBallot OBVIOUS
        <5>2. USE DEF OneValuePerBallot
        <5>3. TAKE a1, a2 \in Acceptor, bb \in Ballot, v1, v2 \in Value
        <5>4. HAVE VotedFor(a1, bb, v1)' /\ VotedFor(a2, bb, v2)'
        <5>5. VotedFor(a1, bb, v1) /\ VotedFor(a2, bb, v2)
          BY ONLY <5>3, <5>4, <4>b
        <5>. QED
          BY ONLY <5>3, <5>5, <5>1
      <4>4. QED
        BY <4>1, <4>2, <4>3
    <3>2. ASSUME NEW a \in Acceptor, NEW b \in Ballot, NEW v \in Value,
                 VoteFor(a, b, v)
          PROVE  Inv'

      <4>1. TypeOK'
\* Zenon failure
        BY <2>2, <3>2 DEF TypeOK, VoteFor (*{ by (isabelle "auto") }*)

      <4>3. OneValuePerBallot'

          <5>1 USE DEF OneValuePerBallot
          <5>2 TAKE a1 \in Acceptor, a2 \in Acceptor, b_1 \in Nat, v1 \in Value, v2 \in Value
          <5>3 SUFFICES ASSUME VotedFor(a1, b_1, v1)', VotedFor(a2, b_1, v2)' PROVE v1 = v2 BY <5>3
          <5>4 USE DEF VotedFor, VoteFor

          <5>5 CASE a1 # a

              <6>1 CASE a2 # a
                  <7>1 votes'[a1] = votes[a1]
                       BY ONLY <2>2, <3>2, votes' = [votes EXCEPT ![a] = votes[a] \union {<<b, v>>}], a1 # a,
                       a \in Acceptor, a1 \in Acceptor, TypeOK DEF TypeOK
                  <7>2 votes'[a2] = votes[a2]
                       BY ONLY <2>2, <3>2, votes' = [votes EXCEPT ![a] = votes[a] \union {<<b, v>>}], a2 # a,
                       a \in Acceptor, a2 \in Acceptor, TypeOK DEF TypeOK
                  <7> QED BY <7>1, <7>2, <5>3

              <6>2 CASE a2 = a

                  <7>1 votes'[a1] = votes[a1]
                       BY ONLY <2>2, <3>2, votes' = [votes EXCEPT ![a] = votes[a] \union {<<b, v>>}], a1 # a,
                       a \in Acceptor, a1 \in Acceptor, TypeOK DEF TypeOK
                  <7>2 votes'[a2] = votes[a2] \union {<<b,v>>}
                       BY ONLY a2 = a, <2>2, <3>2, votes' = [votes EXCEPT ![a] = votes[a] \union {<<b, v>>}],
                       a \in Acceptor, TypeOK DEF TypeOK
                  <7>3 CASE b_1 = b
                       <8>1 <<b, v1>> \in votes[a1] BY <7>1, <5>3, <7>3
                       <8>2 a1 \in Acceptor \ {a} BY <5>5
                       <8>3 <<b, v1>>[1] = b BY auto
                       <8>4 <<b, v1>>[2] = v1 BY auto
                       <8>5 v1 = v BY <8>1, <8>2, <8>3, <8>4, <2>2, <3>2
                       <8>6 <<b,v2>> \in votes[a2] \union {<<b,v>>} BY <7>2, <5>3, <7>3
                       <8>7 ~ (<<b,v2>> \in votes[a2]) BY <3>2, <6>2, <7>3, auto
                       <8>8 <<b, v>> = <<b,v2>> BY <8>6, <8>7
                       <8>9 v = v2 BY ONLY <8>8, auto
                       <8> QED BY <8>9, <8>5

                  <7>4 CASE b_1 # b
                       <8>1 <<b_1, v2>> # <<b,v>> BY <7>4, auto
                       <8>2 <<b_1, v2>> \in votes[a2] BY <8>1, <7>2, <5>3
                       <8>3 <<b_1, v1>> \in votes[a1] BY <7>1, <5>3
                       <8> QED BY <8>2, <8>3


                  <7> QED BY <7>3, <7>4

              <6> QED BY <6>1, <6>2

          <5>6 CASE a1 = a

              <6>1 CASE a2 # a
                  <7>1 votes'[a2] = votes[a2]
                       BY ONLY <3>2, a2 # a,
                       a \in Acceptor, a2 \in Acceptor, TypeOK, auto DEF TypeOK
                  <7>2 votes'[a1] = votes[a1] \union {<<b,v>>}
                       BY ONLY a1 = a, <3>2,
                       a \in Acceptor, TypeOK, auto DEF TypeOK
                  <7>3 CASE b_1 = b
                       <8>1 <<b, v2>> \in votes[a2] BY <7>1, <5>3, <7>3
                       <8>2 a2 \in Acceptor \ {a} BY <6>1
                       <8>3 <<b, v2>>[1] = b BY auto
                       <8>4 <<b, v2>>[2] = v2 BY auto
                       <8>5 v2 = v BY <8>1, <8>2, <8>3, <8>4, <2>2, <3>2
                       <8>6 <<b,v1>> \in votes[a1] \union {<<b,v>>} BY <7>2, <5>3, <7>3
                       <8>7 ~ (<<b,v1>> \in votes[a1]) BY <3>2, <5>6, <7>3, auto
                       <8>8 <<b, v>> = <<b,v1>> BY <8>6, <8>7
                       <8>9 v = v1 BY ONLY <8>8, auto
                       <8> QED BY <8>9, <8>5

                  <7>4 CASE b_1 # b
                       <8>1 <<b_1, v1>> # <<b,v>> BY <7>4, auto
                       <8>2 <<b_1, v1>> \in votes[a1] BY <8>1, <7>2, <5>3
                       <8>3 <<b_1, v2>> \in votes[a2] BY <7>1, <5>3
                       <8> QED BY <8>2, <8>3
                  <7> QED BY <7>3, <7>4

              <6>2 CASE a2 = a
                  <7>1 votes'[a1] = votes[a1] \union {<<b,v>>}
                       BY ONLY a1 = a, <3>2,
                       a \in Acceptor, TypeOK, auto DEF TypeOK
                  <7>2 votes'[a2] = votes[a2] \union {<<b,v>>}
                       BY ONLY a2 = a, <3>2,
                       a \in Acceptor, TypeOK, auto DEF TypeOK
                  <7>3 CASE b_1 = b
                       <8>1 ~ (<<b,v1>> \in votes[a]) BY ONLY <3>2, auto
                       <8>2 <<b,v1>> = <<b,v>> BY <7>1, <8>1, <5>3, <5>6, <7>3
                       <8>3 v1 = v BY ONLY <8>2, auto
                       <8>4 ~ (<<b,v2>> \in votes[a]) BY ONLY <3>2, auto
                       <8>5 <<b,v2>> = <<b,v>> BY <7>2, <8>4, <5>3, <6>2, <7>3
                       <8>6 v2 = v BY ONLY <8>5, auto
                       <8> QED BY <8>3, <8>6

                  <7>4 CASE b_1 # b
                       <8>1 <<b_1,v1>> \in votes[a]
                            <9>1 <<b_1, v1>> \in votes[a] \union {<<b, v>>} BY <7>1, <5>6, <5>3
                            <9>2 <<b_1, v1>> # <<b,v>> BY <7>4, auto
                            <9> QED BY <9>1, <9>2
                       <8>2 <<b_1,v2>> \in votes[a]
                            <9>1 <<b_1, v2>> \in votes[a] \union {<<b, v>>} BY <7>2, <6>2, <5>3
                            <9>2 <<b_1, v2>> # <<b,v>> BY <7>4, auto
                            <9> QED BY <9>1, <9>2
                       <8> QED BY <8>1, <8>2


                  <7> QED BY <7>3, <7>4

              <6> QED BY <6>1, <6>2

          <5> QED BY <5>5, <5>6

      <4>votesMon \A aa \in Acceptor : votes[aa] \subseteq votes'[aa]
            <5>1 SUFFICES ASSUME NEW aa \in Acceptor PROVE votes[aa] \subseteq votes'[aa] BY <5>1
            <5> USE DEF VoteFor
            <5>2 CASE a = aa
                 <6>1 votes'[a] = votes[a] \union {<<b,v>>} BY a \in Acceptor, TypeOK, <3>2, auto DEF TypeOK
                 <6> QED BY <6>1, <5>2
            <5>3 CASE a # aa
                 <6>1 votes[aa] = votes'[aa] BY aa \in Acceptor, TypeOK, <3>2, <5>3, auto DEF TypeOK
                 <6> QED BY <6>1
            <5> QED BY <5>2, <5>3

      <4>maxBalMon \A aa \in Acceptor : maxBal[aa] <= maxBal'[aa]
            <5>1 SUFFICES ASSUME NEW aa \in Acceptor PROVE maxBal[aa] <= maxBal'[aa] BY <5>1
            <5>2 USE DEF VoteFor
            <5>3 CASE a = aa
                 <6>1 maxBal'[aa] = b BY aa \in Acceptor, TypeOK, <3>2, <5>3, auto DEF TypeOK
                 <6> QED BY <6>1, <5>3, <3>2, auto
            <5>4 CASE a # aa
                 <6>1 maxBal[aa] = maxBal'[aa] BY aa \in Acceptor, TypeOK, <5>4, <3>2, auto DEF TypeOK
                 <6>2 /\ maxBal[aa] \in Nat \cup {-1}
                      /\ maxBal'[aa] \in Nat \cup {-1}
                   BY <6>1, TypeOK DEF TypeOK
                 <6>3 \A m, n \in Nat \cup {-1} : m = n => m <= n
                   OBVIOUS (*{ by (cooper) }*)
                 <6> QED \* OMITTED BY <6>1, TypeOK DEF TypeOK
                   BY <6>1, <6>2, <6>3
            <5> QED BY <5>3, <5>4

      <4>stability \A bb \in Ballot, vv \in Value : SafeAt(bb,vv) => SafeAt(bb,vv)'
            <5>1 SUFFICES ASSUME NEW bbb \in Ballot,
                       NEW vvv \in Value,
                       SafeAt(bbb,vvv)
                       PROVE SafeAt(bbb,vvv)'
                       BY <5>1
            <5>2 USE <5>1 DEF SafeAt
            <5>3 SUFFICES ASSUME NEW c \in 0..(bbb-1)
                       PROVE NoneOtherChoosableAt(c,vvv)'
                       BY <5>3
            <5>4 USE DEF NoneOtherChoosableAt
            <5>5 PICK Q \in Quorum : \A aa \in Q : VotedFor(aa, c, vvv) \/ CannotVoteAt(aa, c) OBVIOUS
            <5>6 WITNESS Q \in Quorum
            <5>7 SUFFICES ASSUME NEW aaa \in Q PROVE VotedFor(aaa, c, vvv)' \/ CannotVoteAt(aaa, c)' BY <5>7
            <5>8 VotedFor(aaa, c, vvv) \/ CannotVoteAt(aaa, c) BY <5>5
            <5>9 CASE VotedFor(aaa, c, vvv)
                 <6>1 USE DEF VotedFor
                 <6>2 <<c, vvv>> \in votes'[aaa]
                      <7>1 aaa \in Acceptor BY QuorumAssumption
                      <7> QED BY <7>1, <4>votesMon, <5>9
                 <6> QED BY <6>2
            <5>10 CASE CannotVoteAt(aaa, c)
                 <6>1 CannotVoteAt(aaa, c)'
                      <7>1 USE DEF CannotVoteAt
                      <7>2 maxBal'[aaa] > c
                            <8>1 maxBal[aaa] <= maxBal'[aaa] BY <4>maxBalMon, QuorumAssumption
                            <8>2 maxBal[aaa] > c
                              BY CannotVoteAt(aaa, c)
                            <8>3 /\ maxBal[aaa]  \in Nat \cup {-1}
                                 /\ maxBal[aaa]' \in Nat \cup {-1}
                              BY TypeOK, TypeOK', QuorumAssumption DEF TypeOK
                            <8>4 \A n, m \in Nat \cup {-1} :
                                    m > c /\ m <= n => n > c
                              OBVIOUS (*{ by (cooper) }*)
                            <8> QED (* OMITTED BY ONLY maxBal[a] > c, maxBal[a] \leq maxBal'[a] : strage...*)
                              BY <8>1, <8>2, <8>3, <8>4

                      <7>3 DidNotVoteAt(aaa, c)'
                            <8>0 aaa \in Acceptor BY QuorumAssumption
                            <8>1 USE DEF DidNotVoteAt
                            <8>2 SUFFICES ASSUME NEW vv \in Value PROVE \neg (VotedFor(aaa, c, vv)') BY <8>2
                            <8>3 SUFFICES ASSUME VotedFor(aaa, c, vv)' PROVE FALSE BY <8>3
                            <8>4 \neg VotedFor(aaa, c, vv) BY <5>10
                            <8>6 c # bbb BY ONLY c \in 0 .. bbb-1 (*{by (cooper)}*)
\***                        <8>7 <<c,vv>> # <<b,v>> OMITTED (* should reasonably work *)
                            <8>n USE DEFS VotedFor, VoteFor
                            <8>8 CASE a = aaa
                                 <9>01 b > c
                                   BY <8>8, <7>2, VoteFor(a, b, v), TypeOK
                                       DEF TypeOK
                                 <9>02 b # c
                                   BY <9>01 (*{by (cooper)}*)
                                 <9>a <<c,vv>> # <<b,v>> \* OMITTED
                                    BY <9>02
                                 <9>0 votes'[a] = votes[a] \union {<<b, v>>} BY a \in Acceptor, TypeOK, <3>2, auto DEF TypeOK
                                 <9>1 <<c, vv>> \in votes'[a] BY a \in Acceptor, TypeOK, <8>3, <8>8 DEF TypeOK
                                 <9>2 <<c, vv>> \in votes[a]
                                   BY <9>a, <9>1, <9>0
                                 <9> QED BY <8>4, <9>2, <8>8
                            <8>9 CASE a # aaa
                                 <9>0 votes'[aaa] = votes[aaa] BY <8>0, TypeOK, <8>9, <3>2, auto DEF TypeOK
                                 <9>1 <<c, vv>> \in votes[aaa] BY <9>0, <8>3
                                 <9> QED BY <9>1, <8>4
                            <8> QED BY <8>8, <8>9
                      <7> QED BY <7>2, <7>3
                 <6> QED BY <6>1
            <5> QED BY <5>8, <5>9, <5>10


      <4>tristan VotesSafe'
          <5>1 USE DEF VotesSafe, VotedFor, VoteFor
          <5>2 SUFFICES ASSUME NEW aa \in Acceptor,
                              NEW bb \in Ballot,
                              NEW vv \in Value,
                              VotedFor(aa, bb, vv)'
                       PROVE SafeAt(bb, vv)' BY <5>2
          <5>3 SafeAt(b,v)
              <6>1 PICK Q \in Quorum : ShowsSafeAt(Q, b, v) BY <3>2
              <6> QED BY <6>1, ShowsSafety


          <5>4 CASE b = bb
               <6>1 <<bb,v>> = <<b,v>> BY <5>4
               <6>2 <<bb,v>> \in votes'[a] BY ONLY <6>1, <3>2,
                          a \in Acceptor, TypeOK, auto DEF TypeOK
               <6>3 VotedFor(a,bb,v)' BY <6>2 DEF VotedFor
               <6>4 v = vv BY <6>3, <4>3, <5>2 DEF OneValuePerBallot
               <6>5 SafeAt(b,v) BY <6>4, <5>3
               <6> QED BY <6>5, <6>4, <4>stability, <5>4

          <5>5 CASE b # bb
               <6>1 <<bb,vv>> \in votes[aa] \union {<<b,v>>} BY aa \in Acceptor, TypeOK, <5>2, <3>2, auto DEF TypeOK
               <6>2 <<bb, vv>> # <<b,v>> BY <5>5, auto
               <6>3 <<bb,vv>> \in votes[aa] BY ONLY <6>1, <6>2
               <6>4 SafeAt(bb,vv) BY <6>3, VotesSafe
               <6> QED BY <6>4, <4>stability

          <5> QED BY <5>4, <5>5

      <4>4. QED
        BY <4>1, <4>tristan, <4>3
    <3>3. QED
      BY <3>1, <3>2, <2>2 DEF Next
  <2>3. QED
    BY <2>1, <2>2, <1>2

<1>3. QED
 OMITTED

----------------------------------------------------------------------------

C == INSTANCE Consensus

THEOREM Init => C!Init
<1>1 SUFFICES ASSUME Init PROVE C!Init BY <1>1
<1>2 USE DEFS Init, C!Init, chosen, ChosenAt, VotedFor
<1>3 \A v \in Value : ~ \E b \in Ballot : \E Q \in Quorum : \A a \in Q : <<b, v>> \in votes[a]
     <2>1 TAKE v \in Value
     <2>2 SUFFICES ASSUME \E b \in Ballot : \E Q \in Quorum : \A a \in Q : <<b, v>> \in votes[a] PROVE FALSE BY <2>2
     <2>3 PICK b \in Ballot : \E Q \in Quorum : \A a \in Q : <<b, v>> \in votes[a] OBVIOUS
     <2>4 PICK Q \in Quorum : \A a \in Q : <<b, v>> \in votes[a] OBVIOUS
     <2>5 Q # {} BY QuorumNonEmpty DEF QuorumNonEmpty
     <2>6 \E a \in Acceptor : a \in Q BY <2>5, QuorumAssumption
     <2>7 PICK a \in Acceptor : a \in Q BY <2>6
     <2> QED BY <1>1, <2>4, <2>7
<1> QED BY <1>3

THEOREM Next /\ Inv /\ Inv'=> C!Next \/ UNCHANGED chosen
<1>1 SUFFICES ASSUME Next, Inv, Inv' PROVE C!Next \/ UNCHANGED chosen BY <1>1
<1>2 chosen \subseteq chosen'
    <2>1 USE DEF Next
    <2>2 PICK a \in Acceptor, b \in Ballot :
            \/ IncreaseMaxBal(a, b)
            \/ \E v \in Value : VoteFor(a, b, v) OBVIOUS
    <2>3 CASE IncreaseMaxBal(a, b) BY <2>3 DEF IncreaseMaxBal, chosen, ChosenAt, VotedFor, Ballot
    <2>4 CASE \E v \in Value : VoteFor(a, b, v)
         <3>1 PICK vv \in Value : VoteFor(a, b, vv) OBVIOUS
         <3>2 USE DEF VoteFor, chosen
         <3>3 \A v \in Value : (\E b_1 \in Ballot : ChosenAt(b_1, v)) => \E b_1 \in Ballot' : ChosenAt(b_1, v)'
              <4>1 TAKE v \in Value
              <4>2 SUFFICES
                   ASSUME \E b_1 \in Ballot : ChosenAt(b_1, v) PROVE \E b_1 \in Ballot' : ChosenAt(b_1, v)'
                   BY <4>2
              <4>3 PICK bb \in Ballot : ChosenAt(bb, v) OBVIOUS
              <4>4 USE DEF Ballot, ChosenAt
              <4>5 PICK Q \in Quorum : \A aa \in Q : VotedFor(aa, bb, v) OBVIOUS
              <4>6 USE DEF VotedFor
              <4>7 \A aa \in Q : <<bb, v>> \in votes'[aa]
                   <5>1 TAKE aa \in Q
                   <5>2 <<bb, v>> \in votes[aa] BY <4>5
                   <5>3 CASE aa = a
                         <6>0 aa \in Acceptor BY QuorumAssumption
                         <6>1 votes[aa] \subseteq votes'[aa] BY <6>0, <3>1, <5>3, Inv DEF Inv, TypeOK
                         <6> QED BY <6>1, <5>2
                   <5>4 CASE aa # a
                         <6>0 aa \in Acceptor BY QuorumAssumption
                         <6>1 votes'[aa] = votes[aa] BY <6>0, <3>1, <5>4, Inv DEF Inv, TypeOK
                         <6> QED BY <6>1, <5>2
                   <5> QED BY <5>3, <5>4
              <4> QED BY <4>7, auto
         <3> QED BY <3>3
    <2> QED BY <2>2, <2>3, <2>4
<1>3 USE <1>1 DEF Inv, C!Next
<1>4 OneVote BY OneVoteThm
<1>5 OneVote' OMITTED (* Temporal reasoning *)
<1>6 chosen = {} \/ \E v \in Value : chosen = {v} BY <1>4, VotesSafeImpliesConsistency
<1>7 chosen' = {} \/ \E v \in Value : chosen' = {v} OMITTED (* Temporal reasoning *)
<1>8 CASE chosen = {} /\ chosen' = {} BY <1>8
<1>9 CASE /\ \E v \in Value : chosen = {v}
          /\ \E v \in Value : chosen' = {v}
    <2>1 PICK v1 \in Value : chosen = {v1} BY <1>9
    <2>2 PICK v2 \in Value : chosen' = {v2} BY <1>9
    <2>3 CASE v1 = v2 BY <2>1, <2>2, <2>3
    <2>4 CASE v1 # v2 BY <1>2, <2>1, <2>2, <2>4
    <2> QED BY <2>3, <2>4
<1>10 CASE chosen = {} /\ \E v \in Value : chosen' = {v} BY <1>10
<1>11 CASE \E v \in Value : chosen = {v} /\ chosen' = {} BY <1>2, <1>11
<1> QED BY <1>6, <1>7, <1>8, <1>9, <1>10, <1>11

=============================================================================
