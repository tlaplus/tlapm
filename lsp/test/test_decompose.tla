---- MODULE test_decompose ----

Some == TRUE

\********************** \A

THEOREM TestGoalForAllBounded ==
    ASSUME NEW S PROVE \A a, b \in S : a
PROOF
  <1> TAKE a, b \in S
  <1> QED

THEOREM TestGoalForAllUnbounded ==
    ASSUME NEW S PROVE \A a, b : a
PROOF
  <1> TAKE a, b
  <1> QED

(* Test case: The decompose step should derive `TAKE a_1 \in S`, note `a_1`. *)
THEOREM TestGoalForAllNameClash ==
  ASSUME NEW P(_), NEW S
  PROVE \A a \in S : P(a)
PROOF
  <1> a == TRUE
      a_1 == TRUE
  <1> HIDE DEF a, a_1
  \* --------------
  <1> TAKE a_2 \in S
  <1>q. QED OBVIOUS


\********************** \E

(* TODO: PROOF is not counted to the proof step range. *)
THEOREM TestGoalExists ==
  ASSUME NEW P(_, _), NEW S
  PROVE \E a, b \in S : P(a, b)
PROOF
  <1> a == "TODO: Replace this with actual witness"
  <1> b == "TODO: Replace this with actual witness"
  <1> HIDE DEFS a, b
  <1>4. a \in S 
  <1>5. b \in S 
  <1> WITNESS a \in S, b \in S
  <1>3. QED

THEOREM TestGoalExistsUnderDEF ==
  ASSUME NEW P(_, _), NEW S
  PROVE \E a, b \in S : P(a, b)
PROOF
  <1> DEFINE SS == \E a, b \in S : P(a, b)
  <1> SUFFICES SS OBVIOUS
  <1> HIDE DEF SS
  \* -----------
  <1> a == "TODO: Replace this with actual witness"
  <1> b == "TODO: Replace this with actual witness"
  <1> HIDE DEFS a, b
  <1>1. a \in S
  <1>2. b \in S
  <1>3. USE DEF SS
  <1> WITNESS a \in S, b \in S
  <1>4. QED BY DEF SS

THEOREM TestGoalExistsUnderOP ==
  ASSUME NEW P(_, _), NEW S
  PROVE \E a, b \in S : P(a, b)
PROOF
  <1> DEFINE D(X) == \E a, b \in X : P(a, b)
  <1> SUFFICES D(S) OBVIOUS
  <1> HIDE DEF D
  \* -----------
  <1> a == "TODO: Replace this with actual witness"
  <1> b == "TODO: Replace this with actual witness"
  <1> HIDE DEFS a, b
  <1>1. a \in S
  <1>2. b \in S
  <1>3. USE DEF D
  <1> WITNESS a \in S, b \in S
  <1>4. QED BY DEF D


\* Test case: a symbol bound by \E already defined in the context.
\* Th decomposition has to pick new/fresh name.
THEOREM TestGoalExistsNameClash ==
  ASSUME NEW P(_, _), NEW S
  PROVE \E a, b \in S : P(a, b)
PROOF
  <1> a == TRUE
  <1> a_1 == TRUE
  <1> HIDE DEF a, a_1
  \* -----------
  <1> a_2 == "TODO: Replace this with actual witness for a_2"
  <1> b == "TODO: Replace this with actual witness for b"
  <1> HIDE DEFS a_2, b
  <1>1. a_2 \in S
  <1>2. b \in S
  <1> WITNESS a_2 \in S, b \in S
  <1>3. QED OBVIOUS \* Decompose here.


(* Alternative is to use SUFFICES, but we don't go this way,
   because we have to analyze then what's in the quantified expression. *)
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



\********************** Assm \/

THEOREM TestAssmDisj ==
    ASSUME NEW a, NEW b, NEW c, a \/ b
    PROVE c
PROOF
    <1>1. CASE a 
    <1>2. CASE b 
    <1> QED BY <1>1, <1>2

\********************** Assm =>

THEOREM TestAssmImplies ==
    ASSUME NEW a, NEW b, NEW c, NEW d, a => b => c => d
    PROVE d
PROOF
    <1> QED OMITTED

THEOREM TestAssmImplies2 ==
    ASSUME NEW a, NEW b, NEW c, NEW d, ((a => b) => c) => d
    PROVE d
PROOF
    <1> QED OMITTED



\********************** Assm \E

THEOREM TestAssmExists ==
    ASSUME NEW S, \E x \in S : TRUE
    PROVE S # {}
PROOF
    <1>1. PICK x \in S : TRUE OBVIOUS
    <1> QED BY <1>1


\********************** Assm \A

THEOREM TestAssmForall ==
    ASSUME
      NEW S,
      NEW P(_),
      \A x \in S : P(x),
      NEW a \in S
    PROVE P(a)
PROOF
    <1>1. PICK x \in S : P(x)
          <2>1. \E x \in S : TRUE OMITTED
          <2>2. QED BY <2>1
    <1> QED BY <1>1



\* ------------------------------------- TODO: debug, temp

DebugOp(S) == \A a, b \in S : a

THEOREM DebugTh1 ==
    ASSUME NEW S, S = S PROVE DebugOp(S)
PROOF
  \* <1> TAKE a, b \in S
  <1> QED \* BY DEF DebugOp

====
