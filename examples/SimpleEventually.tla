--------------------------- MODULE SimpleEventually ----------------------------
(* How to prove a liveness property from safety and fairness. *)
EXTENDS TLAPS


VARIABLE x


Init == x = FALSE
Next == x = FALSE /\ x' = TRUE
System == Init /\ [][Next]_x /\ WF_x(Next)


THEOREM System => <>(x = TRUE)
<1>1. SUFFICES (System /\ []~(x = TRUE)) => FALSE
    BY <1>1, PTL
<1> DEFINE TypeOK == x \in BOOLEAN
<1> HIDE DEF TypeOK
<1>2. (Init /\ [][Next]_x) => []TypeOK
    <2>1. Init => TypeOK
        BY DEF Init, TypeOK
    <2>2. ASSUME TypeOK /\ [Next]_x
          PROVE TypeOK'
        BY <2>2 DEF TypeOK, Next
    <2> QED
        BY <2>1, <2>2, PTL
<1>3. ASSUME TypeOK /\ ~(x = TRUE)
      PROVE ENABLED <<Next>>_x
    BY <1>3, ExpandENABLED DEF Next
<1>4. ASSUME <<Next>>_x
      PROVE (x = TRUE)'
    BY <1>4 DEF Next
<1> QED
    BY <1>2, <1>3, <1>4, PTL DEF System, Init
================================================================================
