---- MODULE test_decompose ----

Some == TRUE

\********************** \A

THEOREM TestGoalForAll ==
    \A a : a
PROOF
  <1> TAKE a
  <1>1. QED OBVIOUS


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
  <1> QED BY DEF Some

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
  <1>2. SUFFICES ASSUME ~a ,
                        ~c ,
                        ~d 
                 PROVE  b
  OBVIOUS 
  <1> QED BY <1>2



====
