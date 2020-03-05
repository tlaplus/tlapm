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
<1>1 ASSUME TypeOK
     PROVE WellFormedMessages
  <2> USE <1>1 DEF TypeOK, Message, WellFormedMessages
  <2> TAKE m \in msgs
  <2>0 m \in Message OBVIOUS
  <2> QED BY <2>0
<1> QED BY <1>1

THEOREM TypeInit == Init => TypeOK
<1>1 SUFFICES ASSUME Init PROVE TypeOK BY <1>1
<1>2 USE <1>1 DEF Init
<1>3 maxBal \in [Acceptor -> Ballot \union {-1}] OBVIOUS
<1>4 maxVBal \in [Acceptor -> Ballot \union {-1}] OBVIOUS
<1>5 maxVal \in [Acceptor -> Value \union {None}] OBVIOUS
<1>6 msgs \subseteq Message OBVIOUS
<1> QED BY <1>3, <1>4, <1>5, <1>6 DEF TypeOK


THEOREM TypeInv == Next /\ TypeOK => TypeOK'
<1>1 SUFFICES ASSUME Next, TypeOK PROVE TypeOK' OBVIOUS
<1>2 USE <1>1 DEF Next, TypeOK

<1>3 maxBal' \in [Acceptor -> Ballot' \union {-1}]

  <2>1 CASE \E b \in Ballot : Phase1a(b)
    BY <2>1 DEF Phase1a, Ballot

  <2>2 CASE \E b \in Ballot, v \in Value : Phase2a(b, v)
    <3>1 PICK b \in Ballot, v \in Value : Phase2a(b, v) OBVIOUS
    <3> QED BY <3>1 DEF Phase2a, Ballot

  <2>3 CASE \E a \in Acceptor : Phase1b(a)
    <3>1 PICK a \in Acceptor : Phase1b(a) OBVIOUS
    <3>2 USE DEF Phase1b, Ballot
    <3>3 PICK m \in msgs :
         /\ m[1] = "1a"
         /\ m[2] > maxBal[a]
         /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
         /\ Send(<<"1b", a, m[2], maxVBal[a], maxVal[a]>>)
      BY <3>1
    <3>4 m[2] \in Ballot BY <3>3, WFmsgs DEF WellFormedMessages
    <3> QED BY <3>3, <3>4

  <2>4 CASE \E a \in Acceptor : Phase2b(a)
    <3>1 PICK  a \in Acceptor : Phase2b(a) OBVIOUS
    <3>2 USE DEF Phase2b, Ballot
    <3>3 PICK m \in msgs :
         /\ m[1] = "2a"
         /\ m[2] >= maxBal[a]
         /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
         /\ maxVBal' = [maxVBal EXCEPT ![a] = m[2]]
         /\ maxVal' = [maxVal EXCEPT ![a] = m[3]]
         /\ Send(<<"2b", a, m[2], m[3]>>)
      OBVIOUS
    <3>4 m[2] \in Ballot BY <3>3, WFmsgs DEF WellFormedMessages
    <3> QED BY <3>3, <3>4

  <2>5 QED BY <2>1, <2>2, <2>3, <2>4

<1>4 maxVBal' \in [Acceptor -> Ballot' \union {-1}]

  <2>1 CASE \E b \in Ballot : Phase1a(b)
    BY <2>1 DEF Phase1a, Ballot

  <2>2 CASE \E b \in Ballot, v \in Value : Phase2a(b, v)
    <3>1 PICK b \in Ballot, v \in Value : Phase2a(b, v) OBVIOUS
    <3> QED BY <3>1 DEF Phase2a, Ballot

  <2>3 CASE \E a \in Acceptor : Phase1b(a)
    BY <2>3 DEF Phase1b, Ballot

  <2>4 CASE \E a \in Acceptor : Phase2b(a)
    <3>1 PICK  a \in Acceptor : Phase2b(a) OBVIOUS
    <3>2 USE DEF Phase2b, Ballot
    <3>3 PICK m \in msgs :
         /\ m[1] = "2a"
         /\ m[2] >= maxBal[a]
         /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
         /\ maxVBal' = [maxVBal EXCEPT ![a] = m[2]]
         /\ maxVal' = [maxVal EXCEPT ![a] = m[3]]
         /\ Send(<<"2b", a, m[2], m[3]>>)
      OBVIOUS
    <3>4 m[2] \in Ballot BY <3>3, WFmsgs DEF WellFormedMessages
    <3> QED BY <3>4, <3>3

  <2>5 QED BY <2>1, <2>2, <2>3, <2>4

<1>5 maxVal' \in [Acceptor -> Value \union {None'}]

  <2>1 CASE \E b \in Ballot : Phase1a(b)
    <3>1 PICK b \in Ballot : Phase1a(b) OBVIOUS
    <3> QED BY <3>1 DEF Phase1a, Ballot, None

  <2>2 CASE \E b \in Ballot, v \in Value : Phase2a(b, v)
    <3>1 PICK b \in Ballot, v \in Value : Phase2a(b, v) OBVIOUS
    <3> QED BY <3>1 DEF Phase2a, Ballot, None

  <2>3 CASE \E a \in Acceptor : Phase1b(a)
    <3>1 PICK a \in Acceptor : Phase1b(a) OBVIOUS
    <3> QED BY <3>1 DEF Phase1b, Ballot, None

  <2>4 CASE \E a \in Acceptor : Phase2b(a)
    <3>1 PICK  a \in Acceptor : Phase2b(a) OBVIOUS
    <3>2 USE DEF Phase2b, Ballot, None
    <3>3 PICK m \in msgs :
         /\ m[1] = "2a"
         /\ m[2] >= maxBal[a]
         /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
         /\ maxVBal' = [maxVBal EXCEPT ![a] = m[2]]
         /\ maxVal' = [maxVal EXCEPT ![a] = m[3]]
         /\ Send(<<"2b", a, m[2], m[3]>>)
      OBVIOUS
    <3>4 m[3] \in Value \union {None} BY <3>3, WFmsgs DEF WellFormedMessages
    <3> QED BY <3>3, <3>4

  <2>5 QED BY <2>1, <2>2, <2>3, <2>4

<1>6 msgs' \subseteq Message'

  <2>1 CASE \E b \in Ballot : Phase1a(b)
    <3>1 PICK b \in Ballot : Phase1a(b) OBVIOUS
    <3>2 USE DEF Phase1a, Send, Message, Ballot, None
    <3>3 SUFFICES msgs \union {<<"1a", b>>} \subseteq Message BY <3>1, <3>3
    <3>4 <<"1a", b>> \in Message OBVIOUS
    <3>6 QED BY <3>4

  <2>2 CASE \E b \in Ballot, v \in Value : Phase2a(b, v)
    <3>1 PICK b \in Ballot, v \in Value : Phase2a(b, v) OBVIOUS
    <3>2 USE DEF Phase2a, Send, Message, None
    <3>3 SUFFICES msgs \union {<<"2a", b, v>>} \subseteq Message BY <3>1
    <3>5 <<"2a", b, v>> \in Message BY <3>1
    <3> QED BY <3>5

  <2>3 CASE \E a \in Acceptor : Phase1b(a)
    <3>1 PICK a \in Acceptor : Phase1b(a) OBVIOUS
    <3>2 USE DEF Phase1b, Send, Message, Ballot, None
    <3>3 PICK mrec \in msgs :
           /\ mrec[1] = "1a"
           /\ mrec[2] > maxBal[a]
           /\ maxBal' = [maxBal EXCEPT ![a] = mrec[2]]
           /\ msgs' = msgs \union {<<"1b", a, mrec[2], maxVBal[a], maxVal[a]>>}
      BY <3>1
    <3>4 SUFFICES msgs \union {<<"1b", a, mrec[2], maxVBal[a], maxVal[a]>>}
                  \subseteq Message
      BY <3>3
    <3>6 <<"1b", a, mrec[2], maxVBal[a], maxVal[a]>> \in Message
      BY <3>3, WFmsgs DEF WellFormedMessages
    <3> QED BY <3>6

  <2>4 CASE \E a \in Acceptor : Phase2b(a)
    <3>1 PICK a \in Acceptor : Phase2b(a) OBVIOUS
    <3>2 USE DEF Phase2b, Send, Message, Ballot, None
    <3>3 PICK mrec \in msgs :
        /\ mrec[1] = "2a"
        /\ mrec[2] >= maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = mrec[2]]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = mrec[2]]
        /\ maxVal' = [maxVal EXCEPT ![a] = mrec[3]]
        /\ msgs' = msgs \union {<<"2b", a, mrec[2], mrec[3]>>}
      OBVIOUS
    <3>4 SUFFICES msgs \union {<<"2b", a, mrec[2], mrec[3]>>} \subseteq Message
      BY <3>3
    <3>6 <<"2b", a, mrec[2], mrec[3]>> \in Message
      BY <3>3, WFmsgs DEF WellFormedMessages
    <3> QED BY <3>6
  <2>5 QED BY <2>1, <2>2, <2>3, <2>4

<1>7 WellFormedMessages'

  <2>1 USE DEF WellFormedMessages, None
  <2>2 TAKE m \in msgs'

  <2>3 CASE \E b \in Ballot : Phase1a(b)
    <3>1 PICK b \in Ballot : Phase1a(b) OBVIOUS
    <3>2 USE DEF Phase1a, Ballot, Send
    <3>3 CASE m \in msgs BY <3>3, WFmsgs
    <3>4 CASE m = <<"1a", b>> BY <3>4
    <3> QED BY <3>1, <3>3, <3>4

  <2>4 CASE \E b \in Ballot, v \in Value : Phase2a(b, v)
    <3>1 PICK b \in Ballot, v \in Value : Phase2a(b, v) OBVIOUS
    <3>2 USE DEF Phase2a, Ballot, Send
    <3>3 CASE m \in msgs BY <3>3, WFmsgs
    <3>4 CASE m = <<"2a",b,v>> BY <3>4
    <3> QED BY <3>1, <3>3, <3>4

  <2>5 CASE \E a \in Acceptor : Phase1b(a)

    <3>1 PICK a \in Acceptor : Phase1b(a) OBVIOUS
    <3>2 USE DEF Phase1b, Ballot, Send
    <3>3 PICK mrec \in msgs :
         /\ mrec[1] = "1a"
         /\ mrec[2] > maxBal[a]
         /\ maxBal' = [maxBal EXCEPT ![a] = mrec[2]]
         /\ msgs' = msgs \union {<<"1b", a, mrec[2], maxVBal[a], maxVal[a]>>}
      BY <3>1
    <3>4 CASE m \in msgs BY <3>4, WFmsgs
    <3>5 CASE m = <<"1b", a, mrec[2], maxVBal[a], maxVal[a]>>
      BY <3>3, <3>5, WFmsgs
    <3> QED BY <3>3, <3>4, <3>5

  <2>6 CASE \E a \in Acceptor : Phase2b(a)

    <3>1 PICK a \in Acceptor : Phase2b(a) OBVIOUS
    <3>2 USE DEF Phase2b, Ballot, Send
    <3>3 PICK mrec \in msgs :
         /\ mrec[1] = "2a"
         /\ mrec[2] >= maxBal[a]
         /\ maxBal' = [maxBal EXCEPT ![a] = mrec[2]]
         /\ maxVBal' = [maxVBal EXCEPT ![a] = mrec[2]]
         /\ maxVal' = [maxVal EXCEPT ![a] = mrec[3]]
         /\ msgs' = msgs \union {<<"2b", a, mrec[2], mrec[3]>>}
      OBVIOUS
    <3>4 CASE m \in msgs BY <3>4, WFmsgs
    <3>5 CASE m = <<"2b", a, mrec[2], mrec[3]>> BY <3>5, <3>3, WFmsgs
    <3> QED BY <3>3, <3>4, <3>5

  <2> QED BY <2>3, <2>4, <2>5, <2>6

<1> QED BY <1>3, <1>4, <1>5, <1>6, <1>7


-----------------------------------------------------------

StructOK == \A a \in Acceptor : IF maxVBal[a] = -1
                                THEN maxVal[a] = None
                                ELSE <<maxVBal[a], maxVal[a]>> \in votes[a]

THEOREM StructInit == Init => StructOK BY DEF Init, StructOK

THEOREM StructInv == Next /\ TypeOK /\ StructOK => StructOK'
<1>1 SUFFICES ASSUME Next, TypeOK, StructOK PROVE StructOK' OBVIOUS
<1>2 USE <1>1 DEF Next, StructOK
<1>3 TAKE a \in Acceptor

<1>4 CASE \E b \in Ballot : Phase1a(b)
  <2>1 PICK b \in Ballot : Phase1a(b) OBVIOUS
  <2>2 USE <2>1 DEF Phase1a

  <2>3 CASE maxVBal'[a] = -1 BY <2>3 DEF None, Ballot

  <2>4 CASE maxVBal'[a] # -1
    <3>1 votes[a] = votes[a]'
      <4>1 USE DEF votes, Send
      <4>2 {mm \in {<<"1a", b>>} : mm[1] = "2b" /\ mm[2] = a} = {} OBVIOUS
      <4>3 {mm \in msgs : mm[1] = "2b" /\ mm[2] = a}
           = {mm \in (msgs \union {<<"1a", b>>}) : mm[1] = "2b" /\ mm[2] = a}
        BY <4>2
      <4> QED BY <4>3
    <3> QED BY <3>1, <2>4

  <2> QED BY <2>3, <2>4

<1>5 CASE \E b \in Ballot : \E v \in Value : Phase2a(b, v)
  <2>1 PICK b \in Ballot, v \in Value : Phase2a(b, v) BY <1>5
  <2>2 USE DEF Phase2a, Send, votes, None, Ballot
  <2>3 {mm \in {<<"2a", b, v>>} : mm[1] = "2b" /\ mm[2] = a} = {} OBVIOUS
  <2>4 {mm \in msgs : mm[1] = "2b" /\ mm[2] = a}
       = {mm \in (msgs \union {<<"2a", b,v>>}) : mm[1] = "2b" /\ mm[2] = a}
    BY <2>3
  <2> QED BY <2>1, <2>4

<1>6 CASE \E aa \in Acceptor : Phase1b(aa)
  <2>1 PICK aa \in Acceptor : Phase1b(aa) OBVIOUS
  <2>2 USE DEF Phase1b, Send, votes, None, Ballot
  <2>3 PICK m \in msgs :
         /\ m[1] = "1a"
         /\ m[2] > maxBal[aa]
         /\ maxBal' = [maxBal EXCEPT ![aa] = m[2]]
         /\ Send(<<"1b", aa, m[2], maxVBal[aa], maxVal[aa]>>)
    BY <2>1
  <2> DEFINE newmsg == <<"1b", aa, m[2], maxVBal[aa], maxVal[aa]>>
  <2> USE DEF newmsg
  <2>4 {mm \in {newmsg} : mm[1] = "2b" /\ mm[2] = a} = {} OBVIOUS
  <2>5 {mm \in msgs : mm[1] = "2b" /\ mm[2] = a}
       = {mm \in (msgs \union {newmsg}) : mm[1] = "2b" /\ mm[2] = a}
    BY <2>4
  <2> QED BY <1>6, <2>3, <2>5

<1>7 CASE \E a1 \in Acceptor : Phase2b(a1)
  <2>1 PICK a1 \in Acceptor : Phase2b(a1) OBVIOUS
  <2>2 USE DEF Phase2b, Send, votes, None, Ballot

  <2>3 CASE a = a1
    <3>1 PICK m1 \in msgs :
         /\ m1[1] = "2a"
         /\ m1[2] >= maxBal[a1]
         /\ maxBal' = [maxBal EXCEPT ![a1] = m1[2]]
         /\ maxVBal' = [maxVBal EXCEPT ![a1] = m1[2]]
         /\ maxVal' = [maxVal EXCEPT ![a1] = m1[3]]
         /\ msgs' = msgs \union {<<"2b", a1, m1[2], m1[3]>>}
      OBVIOUS
    <3>2 maxVBal'[a] = m1[2] BY <2>3, <3>1 DEF TypeOK, WellFormedMessages
    <3>3 maxVal'[a] = m1[3] BY <2>3, <3>1 DEF TypeOK, WellFormedMessages
    <3>4 <<m1[2], m1[3]>>
         \in {<<m[3], m[4]>> : m \in {mm \in msgs' : mm[1] = "2b" /\ mm[2] = a}}
      BY <2>3, <3>1, Auto
    <3>5 <<maxVBal'[a], maxVal'[a]>>
         \in {<<m[3], m[4]>> : m \in {mm \in msgs' : mm[1] = "2b" /\ mm[2] = a}}
      BY <3>2, <3>3, <3>4
    <3>6 CASE maxVBal'[a] # -1 BY <3>5, <3>6
    <3>7 CASE maxVBal'[a] = -1
      <4>1 maxVBal'[a] \in Ballot BY <3>2, <3>1, WFmsgs DEF WellFormedMessages
      <4>2 \A x \in Ballot : x = -1 => FALSE BY SimpleArithmetic
      <4> QED BY ONLY <4>1, <4>2, <3>7
    <3> QED BY <3>6, <3>7

  <2>4 CASE a # a1
    <3>1 PICK m \in msgs :
         /\ m[1] = "2a"
         /\ m[2] >= maxBal[a1]
         /\ maxBal' = [maxBal EXCEPT ![a1] = m[2]]
         /\ maxVBal' = [maxVBal EXCEPT ![a1] = m[2]]
         /\ maxVal' = [maxVal EXCEPT ![a1] = m[3]]
         /\ msgs' = msgs \union {<<"2b", a1, m[2], m[3]>>}
      OBVIOUS
    <3>2 maxVBal'[a] = maxVBal[a]
      BY <2>4, <3>1, TypeOK DEF TypeOK
    <3>3 maxVal'[a] = maxVal[a]
      BY <2>4, <3>1, TypeOK DEF TypeOK
    <3>4 {mm \in msgs' : mm[1] = "2b" /\ mm[2] = a}
          = {mm \in msgs : mm[1] = "2b" /\ mm[2] = a}
      BY <3>1, <2>4
    <3> QED BY <3>2, <3>3, <3>4

  <2> QED BY <2>3, <2>4

<1> QED BY <1>1, <1>4, <1>5, <1>6, <1>7

-----------------------------------------------------------

THEOREM OtherMessage == \A m1, m2 \in msgs', a, b \in {"1a","2a","1b","2b"} :
               /\ m1[1] = a /\ m2[1] = b /\ a # b
               /\ msgs' = msgs \union {m2}
               => m1 \in msgs
  <1>1 TAKE m1, m2 \in msgs', a, b \in {"1a","2a","1b","2b"}
  <1>2 SUFFICES ASSUME m1[1] = a, m2[1] = b, a # b, msgs' = msgs \union {m2}
                PROVE m1 \in msgs
    OBVIOUS
  <1> QED BY <1>2

StructOK2 == \A m \in msgs :
   (m[1] = "1b") => /\ maxBal[m[2]] >= m[3]
                    /\ (m[4] >= 0) => <<m[4],m[5]>> \in votes[m[2]]

THEOREM Init => StructOK2 BY DEF Init, StructOK2

THEOREM Next /\ TypeOK /\ StructOK /\ StructOK2 => StructOK2'
  <1>1 SUFFICES ASSUME Next, TypeOK, StructOK, StructOK2 PROVE StructOK2'
    BY <1>1
  <1>2 USE <1>1 DEF StructOK2, Next
  <1>3 TAKE m \in msgs'
  <1>4 SUFFICES ASSUME m[1] = "1b"
                PROVE /\ maxBal'[m[2]] >= m[3]
                      /\ m[4] >= 0 => <<m[4], m[5]>> \in votes'[m[2]]
    OBVIOUS
  <1>5 maxBal'[m[2]] >= m[3]
    <2>1 CASE \E b \in Ballot : Phase1a(b)
      <3>1 PICK b \in Ballot : Phase1a(b) OBVIOUS
      <3>2 USE DEF Phase1a, Send
      <3> QED BY <3>1, <1>4, OtherMessage
    <2>2 CASE \E b \in Ballot : \E v \in Value : Phase2a(b, v)
      <3>1 PICK b \in Ballot, v \in Value : Phase2a(b, v) BY <2>2
      <3>2 USE DEF Phase2a, Send
      <3> QED BY <1>4, <3>1, OtherMessage
    <2>3 CASE \E a \in Acceptor : Phase1b(a)
      <3>1 PICK a \in Acceptor : Phase1b(a) OBVIOUS
      <3>2 USE DEF Phase1b, Send
      <3>3 PICK mm \in msgs :
             /\ mm[1] = "1a"
             /\ mm[2] > maxBal[a]
             /\ maxBal' = [maxBal EXCEPT ![a] = mm[2]]
             /\ msgs'
                  = msgs \union {<<"1b", a, mm[2], maxVBal[a], maxVal[a]>>}
        BY <3>1
      <3>4 CASE m \in msgs
        <4>1 maxBal[m[2]] >= m[3] BY <3>4, <3>3, <1>4, <3>1
        <4>2 CASE a = m[2]
          <5>1 maxBal'[a] = mm[2] BY TypeOK, <3>3 DEF TypeOK
          <5>2 maxBal'[m[2]] = mm[2] BY <5>1, <4>2
          <5>3 mm[2] > maxBal[m[2]] BY <3>3, <4>2
          <5>4 /\ maxBal'[m[2]] \in Nat
               /\ mm[2] \in Nat
               /\ maxBal[m[2]] \in Nat \cup {-1}
               /\ m[3] \in Nat
            BY <1>4, <3>3, <3>4, <5>2 DEF TypeOK, Message, Ballot
          <5> QED OMITTED \*BY <4>1, <5>2, <5>3, <5>4, SimpleArithmetic
        <4>3 CASE a # m[2]
          <5>1 maxBal'[m[2]] = maxBal[m[2]]
               BY TypeOK, <1>4, <3>4, <3>3, <4>3, WFmsgs
               DEF TypeOK, WellFormedMessages
          <5> QED BY <5>1, <4>1
        <4> QED BY <4>2, <4>3
      <3>5 CASE m \in {<<"1b", a, mm[2], maxVBal[a], maxVal[a]>>}
        <4>2 m[2] = a /\ m[3] = mm[2] BY <3>5
        <4>3 maxBal'[a] = mm[2] BY TypeOK, <3>3 DEF TypeOK
        <4> QED OMITTED \*BY <4>2, <4>3
      <3> QED BY <3>4, <3>5, <3>3
    <2>4 CASE \E a \in Acceptor : Phase2b(a)
      <3>1 PICK a \in Acceptor : Phase2b(a) BY <2>4
      <3>2 USE DEF Phase2b, Send
      <3>3 PICK mm \in msgs :
             /\ mm[1] = "2a"
             /\ mm[2] >= maxBal[a]
             /\ maxBal' = [maxBal EXCEPT ![a] = mm[2]]
             /\ maxVBal' = [maxVBal EXCEPT ![a] = mm[2]]
             /\ maxVal' = [maxVal EXCEPT ![a] = mm[3]]
             /\ msgs' = msgs \union {<<"2b", a, mm[2], mm[3]>>}
        BY <3>1
      <3>4 m \in msgs BY <1>4, <3>3, OtherMessage
      <3>5 maxBal[m[2]] >= m[3] BY <1>4, <3>4
      <3>6 CASE m[2] = a
        <4>1 maxBal'[m[2]] = mm[2] BY <3>3, <3>6 DEF TypeOK
        <4>2 mm[2] >= maxBal[m[2]] BY <3>3, <3>6
        <4> QED OMITTED \* BY <4>1, <4>2, <3>5, SimpleArithmetic
      <3>7 CASE m[2] # a
        <4>1 maxBal'[m[2]] = maxBal[m[2]]
          BY <3>3, <3>7, <1>4, WFmsgs DEF TypeOK, WellFormedMessages
        <4> QED BY <3>5, <4>1
      <3> QED BY <3>6, <3>7
    <2> QED BY <2>1, <2>2, <2>3, <2>4
  <1>6 m[4] >= 0 => <<m[4], m[5]>> \in votes'[m[2]]
    <2>1 CASE \E b \in Ballot : Phase1a(b)
      <3>1 PICK b \in Ballot : Phase1a(b) BY <2>1
      <3>2 USE DEF Phase1a, Send, TypeOK, WellFormedMessages
      <3>3 m \in msgs BY <3>1, <1>4, OtherMessage
      <3>4 votes'[m[2]] = votes[m[2]] BY <3>1, <1>4, Auto DEF votes
      <3> QED BY <1>4, <3>3, <3>4
    <2>2 CASE \E b \in Ballot : \E v \in Value : Phase2a(b, v)
      <3>1 PICK b \in Ballot, v \in Value : Phase2a(b, v) BY <2>2
      <3>2 USE DEF Phase2a, Send, TypeOK, WellFormedMessages
      <3>3 m \in msgs BY <3>1, <1>4, OtherMessage
      <3>4 votes'[m[2]] = votes[m[2]] BY <3>1, <1>4, Auto DEF votes
      <3> QED BY <1>4, <3>3, <3>4
    <2>3 CASE \E a \in Acceptor : Phase1b(a)
      <3>1 PICK a \in Acceptor : Phase1b (a) BY <2>3
      \* TODO
      <3> QED
    <2>4 CASE \E a \in Acceptor : Phase2b(a)
      <3>1 PICK a \in Acceptor : Phase2b(a) OBVIOUS
      \* TODO
      <3> QED
    <2> QED BY <2>1, <2>2, <2>3, <2>4
  <1> QED BY <1>5, <1>6

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


Inv == TypeOK /\ StructOK /\ StructOK2 /\ StructOK3 /\ StructOK4 /\ StructOK5

THEOREM \A b \in Ballot, v \in Value : Phase2a(b,v) /\ Inv => \E Q \in Quorum : V!ShowsSafeAt(Q,b,v)
<1>1 TAKE b \in Ballot, v \in Value
<1>2 SUFFICES ASSUME Phase2a(b,v), Inv PROVE \E Q \in Quorum : V!ShowsSafeAt(Q,b,v) BY <1>2
<1>3 USE <1>2 DEF Phase2a, V!ShowsSafeAt
<1>4 PICK Q \in Quorum :
        LET Q1b == {m \in msgs : /\ m[1] = "1b"
                                 /\ m[2] \in Q
                                 /\ m[3] = b}
            Q1bv == {m \in Q1b : m[4] >= 0}
        IN  /\ \A a \in Q : \E m \in Q1b : m[2] = a
            /\ \/ Q1bv = {}
               \/ \E m \in Q1bv :
                    /\ m[5] = v
                    /\ \A mm \in Q1bv : m[4] >= mm[4] OBVIOUS
<1>5 WITNESS Q \in Quorum
<1>6 DEFINE Q1b == {m \in msgs : /\ m[1] = "1b"
                                 /\ m[2] \in Q
                                 /\ m[3] = b}
<1>7 DEFINE Q1bv == {m \in Q1b : m[4] >= 0}
<1>8 \A a \in Q : maxBal[a] >= b
<1>9 \E c \in -1 .. b - 1 :
           /\ c # -1 => (\E a \in Q : V!VotedFor(a, c, v))
           /\ \A d \in c + 1 .. b - 1, a \in Q : V!DidNotVoteAt(a, d)
     <2>1 CASE Q1bv = {}
          <3>1 -1 \in -1 .. (b - 1) BY SimpleArithmetic DEF Inv, TypeOK, Ballot
          <3>2 USE <3>1
          <3>3 WITNESS -1 \in -1 .. (b - 1)
          <3>4 \A d \in -1 + 1 .. b - 1, a \in Q : V!DidNotVoteAt(a, d)
               <4>1 TAKE d \in -1 + 1 .. b - 1, a \in Q
               <4>2 USE DEF V!DidNotVoteAt, V!VotedFor
               <4>3 TAKE v_1 \in Value
               <4>4 SUFFICES ASSUME <<d, v_1>> \in votes[a] PROVE FALSE BY <4>4
               <4>5 \E m \in Q1b : m[2] = a
               <4>6 PICK m \in Q1b : m[2] = a OBVIOUS
               <4>7 maxVBal[a] >= d (* NEW INVARIANT *)
               <4>8 ~ \E mm \in Q1bv : mm[4] >= 0
               <4>9 maxVBal[a] = -1
               <4> QED OMITTED \*** BY <4>7, <4>8
          <3>5 ~ (-1 # -1) OBVIOUS
          <3> QED BY <3>4, <3>5
     <2>2 CASE \E m \in Q1bv :
                    /\ m[5] = v
                    /\ \A mm \in Q1bv : m[4] >= mm[4]
           <3>1 PICK m \in Q1bv :
                    /\ m[5] = v
                    /\ \A mm \in Q1bv : m[4] >= mm[4] OBVIOUS
           <3>2 m[4] \in - 1 .. (b - 1)
           <3>3 USE <3>2
           <3>4 WITNESS m[4] \in - 1 .. (b - 1)
           <3>5 \E a \in Q : V!VotedFor(a, m[4], v)
           <3>6 \A d \in m[4] + 1 .. (b - 1), a \in Q : V!DidNotVoteAt(a, d)
                  <4>1 TAKE d \in m[4] + 1 .. b - 1, a \in Q
                  <4>blurb USE DEF V!DidNotVoteAt
                  <4>2 TAKE v2 \in Value
                  <4>3 SUFFICES ASSUME <<d,v2>> \in votes[a] PROVE FALSE BY <4>3 DEF V!DidNotVoteAt, V!VotedFor
                  <4>4 StructOK5 BY DEF Inv
                  <4>5 USE DEF StructOK5, Inv, TypeOK, WellFormedMessages
                  <4>6 ~ <<d,v2>> \in votes[a]
                         <5>1 USE <4>4 DEF StructOK5 (* C'est PAS LE BON m !!! *)
                         <5>bb m \in msgs
                         <5>2 m[4] < d /\ d < m[3] (* gauche, OK ; droite, prouver m[3] = b, de Q1b, OK*)
                         <5>3 ~ <<d,v2>> \in votes[m[2]] OMITTED \*** BY <5>2, <5>bb
                         <5> QED OMITTED \*** OBVIOUS
                  <4> QED BY <4>6, <4>3
           <3> QED BY <3>5, <3>6
     <2> QED BY <2>1, <2>2, <1>4
<1> QED BY <1>8, <1>9

------------------------------------------------------------

THEOREM Next /\ Inv /\ Inv' => V!Next \/ UNCHANGED <<votes,maxBal>>
<1>1 SUFFICES ASSUME Next, Inv, Inv' PROVE V!Next \/ UNCHANGED <<votes,maxBal>> BY <1>1
<1>2 USE <1>1 DEF Next, V!Next

<1>3 CASE \E b \in Ballot : Phase1a(b)
     <2>1 PICK b \in Ballot : Phase1a(b) OBVIOUS
     <2>2 USE DEF Phase1a
     <2>3 votes' = votes
          <3>1 {mm \in msgs' : /\ mm[1] = "2b"} = {mm \in msgs : /\ mm[1] = "2b"}
                <4>1 USE DEF Send
                <4>2 <<"1a", b>>[1] # "2b" BY Auto
                <4> QED BY <2>1, <4>2
          <3> QED OMITTED \*** BY <3>1 DEF votes
     <2> QED BY <2>3, <2>1

<1>4 CASE \E b \in Ballot : \E v \in Value : Phase2a(b, v)
     <2>1 PICK b \in Ballot, v \in Value : Phase2a(b, v) BY <1>4
     <2>2 USE DEF Phase2a
     <2>3 votes' = votes
          <3>1 {mm \in msgs' : /\ mm[1] = "2b"} = {mm \in msgs : /\ mm[1] = "2b"}
                <4>1 USE DEF Send
                <4>2 <<"2a", b, v>>[1] # "2b" BY Auto
                <4> QED BY <2>1, <4>2, Auto
          <3> QED OMITTED \*** BY <3>1 DEF votes (* PASSE PAS ... *)
     <2> QED BY <2>3, <2>1

<1>5 CASE \E a \in Acceptor : Phase1b(a)
     <2>1 PICK a \in Acceptor : Phase1b(a) OBVIOUS
     <2>2 USE DEF Phase1b
     <2>3 PICK m \in msgs :
               /\ m[1] = "1a"
               /\ m[2] > maxBal[a]
               /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
               /\ Send(<<"1b", a, m[2], maxVBal[a], maxVal[a]>>) BY <2>1
     <2>4 V!IncreaseMaxBal(a,m[2])
         <3>1 USE DEF V!IncreaseMaxBal
         <3>2 votes = votes'
              <4>1 {mm \in msgs' : /\ mm[1] = "2b"} = {mm \in msgs : /\ mm[1] = "2b"}
                  <5>1 USE DEF Send
                  <5>2 <<"1b", a, m[2], maxVBal[a], maxVal[a]>>[1] # "2b" BY Auto
                  <5> QED BY <2>1, <5>2, Auto
              <4> QED OMITTED \*** BY <4>1 DEF votes
         <3> QED BY <3>2, <2>3
     <2>5 \E a2 \in Acceptor, b \in V!Ballot : V!IncreaseMaxBal(a2, b)
         <3>1 WITNESS a \in Acceptor
         <3>2 USE <2>3, WFmsgs DEF Inv, WellFormedMessages, Ballot, V!Ballot
         <3>3 WITNESS m[2] \in V!Ballot
         <3> QED BY <3>1, <3>3, <2>4
     <2> QED BY <2>5

<1>6 CASE \E a \in Acceptor : Phase2b(a)
     <2>1 PICK a \in Acceptor : Phase2b(a) OBVIOUS
     <2>2 USE DEF Phase2b
     <2>3 PICK m \in msgs :
            /\ m[1] = "2a"
            /\ m[2] >= maxBal[a]
            /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
            /\ maxVBal' = [maxVBal EXCEPT ![a] = m[2]]
            /\ maxVal' = [maxVal EXCEPT ![a] = m[3]]
            /\ Send(<<"2b", a, m[2], m[3]>>) OBVIOUS

     <2>4 CASE \E mold \in msgs : mold[1] = "2b" /\ mold[2] = a /\ mold[3] = m[2]
          <3>1 PICK mold \in msgs : mold[1] = "2b" /\ mold[2] = a /\ mold[3] = m[2] OBVIOUS
          <3>2 votes' = votes
               <4>1 USE DEF Send, votes
               <4>2 msgs' = msgs
                    <5>1 \E mold2a \in msgs : mold2a[1] = "2a" /\ mold2a[2] = m[2] /\ mold2a[3] = mold[4]
                         <6>1 \E mo \in msgs :
                                       /\ mo[1] = "2a"
                                       /\ mo[2] = mold[3]
                                       /\ mo[3] = mold[4]
                                 BY <3>1, StructOK4 DEF Inv, StructOK4
                         <6> QED BY <6>1, <3>1
                    <5>2 PICK mold2a \in msgs : mold2a[1] = "2a" /\ mold2a[2] = m[2] /\ mold2a[3] = mold[4] BY <5>1
                    <5>i USE DEF Inv, StructOK3
                    <5>3 mold2a[3] = m[3]
                         OMITTED \***
(***
                         BY ONLY m \in msgs, m[1] = "2a", mold2a \in msgs, mold2a[1] = "2a",
                                 mold2a[2] = m[2], (\A m \in msgs :
                                                       m[1] = "2a"
                                                   => (\A mm \in msgs :
                                                             (/\ mm[1] = "2a"
                                                              /\ mm[2] = m[2]) => mm[3] = m[3]))
*)
                    <5>4 mold = <<"2b",a,m[2],m[3]>> OMITTED (* USE THE LENGTH OF TUPLE *)
                         (* BY ONLY TypeOK, mold[1] = "2b", mold[2] = a, mold[3] = m[2], <5>3, mold[4] = mold2a[3]
                         DEF TypeOK, WellFormedMessages *)
                    <5> QED BY <5>4, <2>3
               <4> QED OMITTED \*** BY <4>2
          <3>3 maxBal' = maxBal
                <4>1 maxBal[mold[2]] >= mold[3] OMITTED \*** BY DEF Inv, StructOK4
                <4>2 maxBal[a] >= m[2] BY <4>1, <3>1
                <4> QED OMITTED (*  Trivial but arithmetic *)
          <3> QED BY <3>2, <3>3


     <2>5 CASE ~ (\E mold \in msgs : mold[1] = "2b" /\ mold[2] = a /\ mold[3] = m[2])

         <3>1 V!VoteFor(a, m[2], m[3])
              <4>1 USE DEF Inv, StructOK3, V!VoteFor, Send
              <4>2 \A vt \in votes[a] : vt[1] # m[2]
                   <5>1 TAKE vt \in votes[a]
                   <5>2 USE DEF votes
                   <5> QED OMITTED \*** OBVIOUS
              <4>3 \A c \in Acceptor \ {a} : \A vt \in votes[c] : vt[1] = m[2] => vt[2] = m[3]
                  <5>1 TAKE c \in Acceptor \ {a}
                  <5>2 TAKE vt \in votes[c]
                  <5>3 SUFFICES ASSUME vt[1] = m[2] PROVE vt[2] = m[3] BY <5>3
                  <5>4 USE DEF votes
                  <5>5 vt \in {<<m2[3], m2[4]>> : m2 \in {mm \in msgs : /\ mm[1] = "2b" /\ mm[2] = c}} BY TypeOK DEF TypeOK
                  <5>6 \E m2 \in msgs : m2 = <<"2b",c,vt[1],vt[2]>>
                  <5>7 PICK mmm \in msgs : mmm = <<"2b",c,vt[1],vt[2]>> BY <5>6
                  <5>8 \E m2 \in msgs : m2 = <<"2a",vt[1],vt[2]>> (* MY INVARIANT *)
                  <5>9 PICK mmmm \in msgs : mmmm = <<"2a",vt[1],vt[2]>> BY <5>8
                  <5>10 \A mm \in msgs :
                             /\ mm[1] = "2a"
                             /\ mm[2] = m[2]
                             => mm[3] = m[3] BY <2>3
                  <5>11 mmmm[3] = m[3]
                    <6>1 mmmm[1] = "2a" BY <5>9, Auto
                    <6>2 mmmm[2] = m[2] BY <5>9, <5>3, Auto
                    <6>3 QED BY <5>10, <6>1, <6>2
                  <5> QED BY <5>11, <5>9, Auto
              <4>4 \E Q \in Quorum : V!ShowsSafeAt(Q, m[2], m[3]) BY <2>3
              <4>5 maxBal[a] \leq m[2] OMITTED \* in the context : m[2] >= maxBal[a] *\
              <4>6 votes' = [votes EXCEPT ![a] = votes[a] \union {<<m[2], m[3]>>}]
              <4> QED BY <4>2, <4>3, <4>4, <4>5, <4>6, <2>3
        <3>2 \E a2 \in Acceptor, b \in V!Ballot, v \in Value : V!VoteFor(a2, b, v)
        <3> QED BY <3>2

     <2> QED BY <2>4, <2>5

<1> QED BY <1>3, <1>4, <1>5, <1>6


============================================================
