--------------------------- MODULE SimpleEventually ----------------------------
(* How to prove a liveness property from safety and fairness. *)
EXTENDS TLAPS


VARIABLE x, y, flip
vars == <<x, y, flip>>

TypeOK ==
    /\ x \in BOOLEAN
    /\ y \in BOOLEAN
    /\ flip \in BOOLEAN

Init ==
    /\ x = FALSE
    /\ y = FALSE
    /\ flip = FALSE

A ==
    /\ x = FALSE
    /\ x' = TRUE
    /\ UNCHANGED <<y, flip>>

B ==
    /\ y = FALSE \* WF_vars(Next) hinges on the fact that a B step disables B, i.e., additional B steps will leave vars unchanged. 
    /\ y' = TRUE
    /\ flip' = ~flip
    /\ UNCHANGED x

C ==
    /\ y = FALSE \* WF_vars(Next) hinges on the fact that a C step disables C. 
    /\ y' = TRUE
    /\ flip' = ~flip
    /\ UNCHANGED x

Next ==
    A \/ B \/ C

System ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

Prop ==
    <>(x = TRUE)

-------------------------------------------------------------------------------
(* Ordinary safety proof. *)
LEMMA TypeCorrect == System => []TypeOK
<1>1. Init => TypeOK BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK' BY DEF TypeOK, Next, vars, A, B, C
<1>. QED BY <1>1, <1>2, PTL DEF System, TypeOK, Init, Next, A, B, C

-------------------------------------------------------------------------------

(* 
    Proof of liveness property. Informally:
    <1>1 proves that x can become true because Next is enabled.
    <1>2 proves that x becomes true by taking a Next step if y is already true.
    <1>3 proves that y will become true eventually.
    <1>4 proves that action B will be disable. Thus, []<>ENABLED <<Next>>_vars... effectively becomes []<>ENABLED <<A>>_vars...
*)
THEOREM System => Prop
<1>1. TypeOK /\ ~(x = TRUE) => ENABLED <<Next>>_vars
  BY ExpandENABLED DEF TypeOK, Next, A, B, C, vars
<1>2. TypeOK /\ ~(x = TRUE) /\ (y = TRUE) /\ <<Next>>_vars => (x = TRUE)'
  BY DEF TypeOK, Next, A, B, C, vars
<1>3. TypeOK /\ ~(x = TRUE) /\ ~(y = TRUE) /\ ~(x = TRUE)' /\ <<Next>>_vars => (y = TRUE)'
  BY DEF TypeOK, Next, A, B, C, vars
<1>4. TypeOK /\ (y = TRUE) /\ [Next]_vars => (y = TRUE)' \* Could replace [Next]_vars with UNCHANGED vars.
  BY DEF TypeOK, Next, A, B, C, vars
<1> QED
  BY TypeCorrect, <1>1, <1>2, <1>3, <1>4, PTL DEF System, Prop

================================================================================
