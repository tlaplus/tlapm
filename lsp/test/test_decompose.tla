---- MODULE test_decompose ----

Some == TRUE

\********************** \A

THEOREM TestGoalForAll ==
    \A a : a
PROOF
  <1> TAKE a
  <1>1. QED


\********************** \E

(* TODO: PROOF is not counted to the proof step range. *)
THEOREM TestGoalExists ==
  ASSUME NEW P(_), NEW S
  PROVE \E a \in S : P(a)
PROOF
  <1> DEFINE a == TRUE
  <1> HIDE DEF a
  <1> a \in S
  <1> WITNESS a \in S
  <1> QED OBVIOUS

THEOREM TestGoalExists2 ==
  ASSUME NEW P(_), NEW S
  PROVE \E a \in S : P(a)
PROOF
    <1> DEFINE a_witness == TRUE
    <1> HIDE DEF a_witness
    <1> SUFFICES a_witness \in S /\ P(a_witness) OBVIOUS
    <1> QED OBVIOUS



\********************** =>

THEOREM TestGoalImplies ==
    \A a : a => a
PROOF
  <1> TAKE a
  <1> HAVE a
  <1>1. QED OBVIOUS

\********************** /\

THEOREM TestGoalConjunction ==
    \A a, b, c \in Some : a /\ b /\ c
PROOF
  <1> TAKE a, b, c \in Some
  <1>1. a BY DEF Some
  <1>2. b BY DEF Some
  <1>3. c BY DEF Some
  <1> QED BY <1>1, <1>2, <1>3

THEOREM TestGoalConjunctionList ==
    \A a, b, c \in Some :
        /\ a
        /\ b
        /\ c
PROOF
  <1> TAKE a, b, c \in Some
  <1>1. a OBVIOUS
  <1>2. b OBVIOUS
  <1>3. c OBVIOUS
  <1> QED BY <1>1, <1>2, <1>3

\********************** \/

THEOREM TestGoalDisjunction ==
    \A a, b, c \in Some : a \/ b \/ c
PROOF
  <1> TAKE a, b, c \in Some
  <1> QED OBVIOUS

THEOREM TestGoalDisjunctionList ==
    \A a, b, c, d \in Some :
      \/ a
      \/ b
      \/ c \/ d
PROOF
    <1> TAKE a, b, c, d \in Some
    <1>1. SUFFICES ASSUME ~b ,
                          ~c ,
                          ~d 
                   PROVE  a
          OBVIOUS
    <1> QED BY <1>1

\********************** <=>

THEOREM TestGoalEquiv ==
  \A a, b \in Some : a <=> b
PROOF
  <1> TAKE a, b \in Some
  <1>1. a => b OBVIOUS
  <1>2. b => a OBVIOUS
  <1> QED BY <1>1, <1>2


THEOREM TestGoalEquiv3 (* TODO: QED Fails to be proved. *) ==
  \A a, b, c \in Some : a <=> b <=> c
PROOF
  <1> TAKE a, b, c \in Some
  <1>1. a => b OBVIOUS
  <1>2. b => c
    <2> HAVE b
    <2> QED OBVIOUS
  <1>3. c => a OBVIOUS
  <1> QED BY <1>1, <1>2, <1>3


====
