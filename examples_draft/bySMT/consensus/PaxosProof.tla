-----------------MODULE PaxosProof-------------------
EXTENDS TLAPS, PaxosTuple

WellFormedMessages == \A m \in msgs :
    /\ m[1] = "1a" => m[2] \in Ballot
    /\ m[1] = "1b" => /\ m[2] \in Acceptor
                      /\ m[3] \in Ballot
                      /\ m[4] \in Ballot \union {-1}
                      /\ m[5] \in Value \union {None}
    /\ m[1] = "2a" => m[2] \in Ballot /\ m[3] \in Value
    /\ m[1] = "2b" => m[2] \in Acceptor /\ m[3] \in Ballot /\ m[4] \in Value

-----------------------------------------------------------------------------

THEOREM WFmsgs == TypeOK => WellFormedMessages
  BY Z3 DEFS Ballot, TypeOK, Message, WellFormedMessages

THEOREM Spec => []TypeOK
<1>. USE DEFS Ballot, TypeOK
<1>1. Init => TypeOK
  BY SMT DEFS Init
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY SMT DEFS Next, Phase1a, Phase2a, Phase1b, Phase2b, Send, Message, vars
<1>3. QED
  PROOF OMITTED     \* Temporal proof

-----------------------------------------------------------

StructOK1 == \A a \in Acceptor : IF maxVBal[a] = -1
                                 THEN maxVal[a] = None
                                 ELSE <<maxVBal[a], maxVal[a]>> \in votes[a]

THEOREM Spec => []StructOK1
<1>. USE DEFS Ballot, TypeOK, StructOK1
<1>1. Init => StructOK1
  BY Z3 DEFS Init
<1>2. TypeOK /\ StructOK1 /\ [Next]_vars => StructOK1'
  BY WFmsgs, Z3T(5) DEFS Next, Phase1a, Phase2a, Phase1b, Phase2b, Send, votes,
    WellFormedMessages, vars, Message
<1>q. QED
  PROOF OMITTED     \* Temporal proof

-----------------------------------------------------------

StructOK2 == \A m \in msgs :
   (m[1] = "1b") => /\ maxBal[m[2]] >= m[3]
                    /\ (m[4] >= 0) => <<m[4],m[5]>> \in votes[m[2]]

StructOK3 == \A m \in msgs : m[1] = "2a" => /\ \E Q \in Quorum : V!ShowsSafeAt(Q,m[2],m[3])
                                            /\ \A mm \in msgs : /\ mm[1] = "2a"
                                                                /\ mm[2] = m[2]
                                                                => mm[3] = m[3]

StructOK4 == \A m \in msgs : m[1] = "2b" => /\ \E mo \in msgs : /\ mo[1] = "2a"
                                                                /\ mo[2] = m[3]
                                                                /\ mo[3] = m[4]
                                            /\ maxBal[m[2]] >= m[3]
                                            /\ maxVBal[m[2]] >= m[3]

StructOK5 == \A m \in msgs : m[1] = "1b" => \A d \in Ballot : m[4] < d /\ d < m[3] =>
                                            \A v \in Value : ~ <<d,v>> \in votes[m[2]]

StructOK == /\ TypeOK
            /\ StructOK1
            /\ StructOK2
\*            /\ StructOK3
            /\ StructOK4
            /\ StructOK5

THEOREM Spec => []StructOK
<1>. USE DEFS Ballot, StructOK, TypeOK, StructOK1, StructOK2, StructOK4, StructOK5
<1>1. Init => StructOK
  BY Z3 DEFS Init
<1>2. StructOK /\ [Next]_vars => StructOK'
  BY WFmsgs, Z3 DEFS Next, Phase1a, Phase2a, Phase1b, Phase2b, Send, votes,
    WellFormedMessages, vars, Message
<1>3. QED
  PROOF OMITTED     \* Temporal proof


THEOREM Spec => []StructOK3
<1>. USE DEFS Ballot, TypeOK, StructOK3
<1>1. Init => StructOK3
  BY Z3 DEFS Init
<1>2. TypeOK /\ StructOK /\ [Next]_vars => StructOK3'
  PROOF OMITTED
<1>3. QED
  PROOF OMITTED     \* Temporal proof


-----------------------------------------------------------------------------

Inv == TypeOK /\ StructOK1 /\ StructOK2 /\ StructOK3 /\ StructOK4 /\ StructOK5

THEOREM OtherMessage == \A m1, m2 \in msgs', a, b \in {"1a","2a","1b","2b"} :
               /\ m1[1] = a /\ m2[1] = b /\ a # b
               /\ msgs' = msgs \union {m2}
               => m1 \in msgs
  BY Z3

THEOREM \A b \in Ballot, v \in Value :
            Phase2a(b,v) /\ Inv => \E Q \in Quorum : V!ShowsSafeAt(Q,b,v)
<1>1. SUFFICES ASSUME NEW b \in Ballot,
                      NEW v \in Value,
                      ~ \E m \in msgs : m[1] = "2a" /\ m[3] = b,
                      NEW Q \in Quorum,
                      LET Q1b == {m \in msgs : /\ m[1] = "1b"
                                               /\ m[2] \in Q
                                               /\ m[3] = b}
                          Q1bv == {m \in Q1b : m[4] \geq 0}
                      IN  /\ \A a \in Q : \E m \in Q1b : m[2] = a
                          /\ \/ Q1bv = {}
                             \/ \E m \in Q1bv :
                                  /\ m[5] = v
                                  /\ \A mm \in Q1bv : m[4] \geq mm[4],
                      Send(<<"2a", b, v>>),
                      UNCHANGED <<maxBal, maxVBal, maxVal>>,
                      Inv
               PROVE  V!ShowsSafeAt(Q,b,v)
  BY SMT DEF Phase2a
<1>. USE <1>1 DEF Ballot, Inv, TypeOK
<1>2. V!ShowsSafeAt(Q,b,v)!1
  BY SMT DEF Ballot, Send, StructOK2
<1>. DEFINE Q1b == {m \in msgs : /\ m[1] = "1b"
                                 /\ m[2] \in Q
                                 /\ m[3] = b}
<1>. DEFINE Q1bv == {m \in Q1b : m[4] \geq 0}
<1>3. V!ShowsSafeAt(Q,b,v)!2
  <2>1. SUFFICES ASSUME NEW c \in -1 .. b - 1
                 PROVE /\ c # -1 => (\E a \in Q : V!VotedFor(a, c, v))
                       /\ \A d \in c + 1 .. b - 1, a \in Q : V!DidNotVoteAt(a, d)
    BY SMT
  <2>2. c # -1 => (\E a \in Q : V!VotedFor(a, c, v))
  <2>3. \A d \in c + 1 .. b - 1, a \in Q : V!DidNotVoteAt(a, d)
  <2>q. QED
    BY <2>2, <2>3, SMT
<1>q. QED
  BY <1>2, <1>3, Z3 DEF V!ShowsSafeAt

------------------------------------------------------------

THEOREM Next /\ Inv => V!Next \/ UNCHANGED <<votes,maxBal>>
<1>1. SUFFICES ASSUME Next, Inv PROVE V!Next
  BY <1>1, SMT
<1>. USE DEF Next, V!Next
<1>2. CASE \E b \in Ballot : Phase1a(b)
<1>3. CASE \E b \in Ballot : \E v \in Value : Phase2a(b, v)
<1>4. CASE \E a \in Acceptor : Phase1b(a)
  BY <1>4, Inv, WFmsgs, Z3T(10)
  DEF Phase1b, Inv, WellFormedMessages, Ballot, V!Ballot, V!IncreaseMaxBal, votes, Send
<1>5. CASE \E a \in Acceptor : Phase2b(a)
  <2>1. PICK a \in Acceptor, m \in msgs :
            /\ m[1] = "2a"
            /\ m[2] \geq maxBal[a]
            /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
            /\ maxVBal' = [maxVBal EXCEPT ![a] = m[2]]
            /\ maxVal' = [maxVal EXCEPT ![a] = m[3]]
            /\ Send(<<"2b", a, m[2], m[3]>>)
    BY <1>5, Z3 DEF Phase2b
  <2>2. SUFFICES ASSUME NEW a_1 \in Acceptor, NEW b \in Nat
                 PROVE  \/ V!IncreaseMaxBal(a_1, b)
                        \/ \E v \in Value : V!VoteFor(a_1, b, v)
    BY Z3 DEF V!Ballot
  <2>q. QED
<1>q. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, Z3


============================================================
