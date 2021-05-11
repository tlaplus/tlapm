------------------------ MODULE MiniProducerConsumer_test -------------------
EXTENDS Integers, Sequences, TLAPS
VARIABLES in, out, buf
CONSTANT N, Msg, Input
vars == << in, out, buf >>

ISeq(S) == [(Nat \ {0}) -> S]

ITail(iseq) == [i \in (Nat \ {0}) |-> iseq[i+1]]

IHead(iseq) == iseq[1]

seq ** iseq == [i \in (Nat \ {0}) |->
                  IF i =< Len(seq) THEN seq[i]
                                   ELSE iseq[i - Len(seq)]]

LEMMA IDistr == ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in ISeq(S)
                PROVE  (s \o t) ** u = s ** (t ** u)
 BY DEF ISeq, **

LEMMA HeadTail == ASSUME NEW S,
                         NEW s \in Seq(S), NEW t \in Seq(S),
                         Len(t) # 0
                  PROVE s \o t = Append(s, Head(t)) \o Tail(t)
OBVIOUS



LEMMA IHeadTail == ASSUME NEW S,
                         NEW s \in Seq(S), NEW t \in ISeq(S)
                  PROVE
                  s ** t = Append(s, IHead(t)) ** ITail(t)
BY DEF IHead, ISeq, ITail, **

AXIOM Assump == /\ N \in Nat \ {0}
                /\ Input \in ISeq(Msg)


Init == (* Global variables *)
        /\ in = Input
        /\ out = << >>
        /\ buf = << >>

Producer == /\ Len(buf) # N
            /\ buf' = Append(buf, IHead(in))
            /\ in' = ITail (in)
            /\ out' = out

Consumer == /\ Len(buf) # 0
            /\ out' = Append(out, Head(buf))
            /\ buf' = Tail (buf)
            /\ in' = in

Next == Producer \/ Consumer

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Producer)
        /\ WF_vars(Consumer)

ProcSet == {0} \cup {1}

TypeOK == /\ in \in ISeq(Msg)
          /\ out \in Seq(Msg)
          /\ buf \in Seq(Msg)

Inv == /\ TypeOK
       /\ (Len(buf) =< N)
       /\ (Input = (out \o buf) ** in)

THEOREM Spec BY PTL

=============================================================================
result: 0
stderr: BEGIN
