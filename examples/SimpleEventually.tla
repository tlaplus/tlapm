--------------------------- MODULE SimpleEventually ----------------------------
(* How to prove a liveness property from safety and fairness. *)
EXTENDS TLAPS


VARIABLE x, y
vars == <<x, y>>

TypeOK ==
    /\ x \in BOOLEAN
    /\ y \in BOOLEAN

Init ==
    /\ x = FALSE
    /\ y = FALSE

A ==
    /\ x = FALSE
    /\ x' = TRUE
    /\ UNCHANGED y

B ==
    /\ y = FALSE
    /\ y' = TRUE
    /\ UNCHANGED x

Next ==
    A \/ B

System ==
    Init /\ [][Next]_vars /\ WF_vars(A)

Prop ==
    <>(x = TRUE)

-------------------------------------------------------------------------------
(* Ordinary safety proof. *)
LEMMA TypeCorrect == System => []TypeOK
<1>1. Init => TypeOK BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK' BY DEF TypeOK, Next, vars, A, B
<1>. QED BY <1>1, <1>2, PTL DEF System, TypeOK, Init, Next, A, B

-------------------------------------------------------------------------------

\* The PM needs this hint for the liveness proof to be accepted.
LEMMA Equiv == ~(x = TRUE) <=> (x = FALSE) OBVIOUS
USE Equiv

-------------------------------------------------------------------------------

(* Proof of liveness property. *)
THEOREM System => Prop
<1>1. SUFFICES (System /\ [](x = FALSE)) => FALSE 
    BY <1>1, PTL DEF Prop
<1>3. ASSUME TypeOK /\ (x = FALSE)
      PROVE ENABLED <<A>>_vars
    BY <1>3, ExpandENABLED DEF Next, vars, A, B
<1>4. ASSUME <<A>>_vars
      PROVE (x = TRUE)'
    BY <1>4 DEF Next, vars, A, B
<1> QED
    BY TypeCorrect, <1>3, <1>4, PTL DEF System, Init, Prop

================================================================================
