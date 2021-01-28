---------------------------------- MODULE Dekker -------------------------------
(* This mutual exclusion algorithm is described in [1, p. 58].


Reference
=========

[1] E. W. Dijkstra, "Co-operating sequential processes"
    in "Programming Languages", Academic Press, 1968
    https://www.cs.utexas.edu/users/EWD/transcriptions/EWD01xx/EWD123.html
*)
EXTENDS Integers, TLAPS


VARIABLE c1, c2, turn, pc1, pc2


vars == <<c1, c2, turn, pc1, pc2>>
vars1 == <<pc1, c1, turn>>
vars2 == <<pc2, c2, turn>>

Init ==
    /\ c1 = 1
    /\ c2 = 1
    /\ turn = 1
    /\ pc1 = 1
    /\ pc2 = 1

Next1 ==
    \/ /\ pc1 = 1  (* label A1 *)
       /\ c1' = 0
       /\ pc1' = 2
       /\ UNCHANGED <<turn>>

    \/ /\ pc1 = 2  (* label L1 *)
       /\ IF c2 = 0
            THEN pc1' = 3
            ELSE pc1' = 6
       /\ UNCHANGED <<c1, turn>>

    \/ /\ pc1 = 3
       /\ IF turn = 1
            THEN pc1' = 2
            ELSE pc1' = 4
       /\ UNCHANGED <<c1, turn>>

    \/ /\ pc1 = 4
       /\ c1' = 1
       /\ pc1' = 5
       /\ UNCHANGED <<turn>>

    \/ /\ pc1 = 5  (* label B1 *)
       /\ IF turn = 2
            THEN pc1' = 5
            ELSE pc1' = 1
       /\ UNCHANGED <<c1, turn>>

    \/ /\ pc1 = 6  (* critical section *)
       /\ pc1' = 7
       /\ UNCHANGED <<c1, turn>>

    \/ /\ pc1 = 7
       /\ pc1' = 8
       /\ turn' = 2
       /\ UNCHANGED <<c1>>

    \/ /\ pc1 = 8
       /\ pc1' = 9
       /\ c1' = 1
       /\ UNCHANGED <<turn>>

    \/ /\ pc1 = 9  (* remainder of cycle 1 *)
       /\ pc1' = 1
       /\ UNCHANGED <<c1, turn>>

Next2 ==
    \/ /\ pc2 = 1  (* label A2 *)
       /\ c2' = 0
       /\ pc2' = 2
       /\ UNCHANGED <<turn>>

    \/ /\ pc2 = 2  (* label L2 *)
       /\ IF c1 = 0
            THEN pc2' = 3
            ELSE pc2' = 6
       /\ UNCHANGED <<c2, turn>>

    \/ /\ pc2 = 3
       /\ IF turn = 2
            THEN pc2' = 2
            ELSE pc2' = 4
       /\ UNCHANGED <<c2, turn>>

    \/ /\ pc2 = 4
       /\ c2' = 1
       /\ pc2' = 5
       /\ UNCHANGED <<turn>>

    \/ /\ pc2 = 5  (* label B2 *)
       /\ IF turn = 1
            THEN pc2' = 5
            ELSE pc2' = 1
       /\ UNCHANGED <<c2, turn>>

    \/ /\ pc2 = 6  (* critical section *)
       /\ pc2' = 7
       /\ UNCHANGED <<c2, turn>>

    \/ /\ pc2 = 7
       /\ pc2' = 8
       /\ turn' = 1
       /\ UNCHANGED <<c2>>

    \/ /\ pc2 = 8
       /\ pc2' = 9
       /\ c2' = 1
       /\ UNCHANGED <<turn>>

    \/ /\ pc2 = 9  (* remainder of cycle 2 *)
       /\ pc2' = 1
       /\ UNCHANGED <<c2, turn>>

Next == \/ Next1 /\ UNCHANGED <<pc2, c2>>
        \/ Next2 /\ UNCHANGED <<pc1, c1>>

Sys ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars1(pc1 # 9 /\ Next1)
    /\ WF_vars2(pc2 # 9 /\ Next2)

Inv == pc1 # 6 \/ pc2 # 6
StFr1 == (pc1 = 2) ~> (pc1 = 6)
StFr2 == (pc2 = 2) ~> (pc2 = 6)

Spec == /\ []Inv
        /\ StFr1
        /\ StFr2

--------------------------------------------------------------------------------
(* Mutual exclusion. *)

(* The values of the variables pc1, pc2, turn
determine the complete state of the system.
*)
IndInv ==
    /\ turn \in 1..2

    /\ pc1 \in 1..9
    /\ c1 \in 0..1

    /\ pc2 \in 1..9
    /\ c2 \in 0..1

    /\ (pc1 = 2) => (c1 = 0)
    /\ (pc1 = 3) => (c1 = 0)
    /\ (pc1 = 4) => (c1 = 0)
    /\ (pc1 = 5) => (c1 = 1)
    /\ (pc1 = 6) => (c1 = 0 /\ pc2 # 6)
    /\ (pc1 = 7) => (c1 = 0)
    /\ (pc1 = 8) => (c1 = 0)
    /\ (pc1 = 9) => (c1 = 1)

    /\ (pc2 = 2) => (c2 = 0)
    /\ (pc2 = 3) => (c2 = 0)
    /\ (pc2 = 4) => (c2 = 0)
    /\ (pc2 = 5) => (c2 = 1)
    /\ (pc2 = 6) => (c2 = 0 /\ pc1 # 6)
    /\ (pc2 = 7) => (c2 = 0)
    /\ (pc2 = 8) => (c2 = 0)
    /\ (pc2 = 9) => (c2 = 1)


THEOREM MutualExclusion ==
    Sys => []Inv
PROOF
<1>1. Sys => []IndInv
    <2>1. ASSUME Init
          PROVE IndInv
        BY <2>1 DEF Init, IndInv
    <2>2. ASSUME IndInv /\ [Next]_vars
          PROVE IndInv'
        BY <2>2 DEF IndInv, Next, Next1, Next2, vars
    <2> QED
        BY <2>1, <2>2, PTL DEF Sys
<1>2. IndInv => Inv
    BY DEF IndInv, Inv
<1> QED
    BY <1>1, <1>2, PTL

--------------------------------------------------------------------------------
(* Always at least one process can take a step that changes the state. *)

Enabledness == ENABLED <<Next>>_vars


THEOREM NotStuck ==
    Sys => []Enabledness
PROOF
<1>1. Sys => []IndInv
    <2>1. ASSUME Init
          PROVE IndInv
        BY <2>1 DEF Init, IndInv
    <2>2. ASSUME IndInv /\ [Next]_vars
          PROVE IndInv'
        BY <2>2 DEF IndInv, Next, Next1, Next2, vars
    <2> QED
        BY <2>1, <2>2, PTL DEF Sys
<1>2. ASSUME IndInv
      PROVE Enabledness
    BY <1>2, ExpandENABLED DEF IndInv, Enabledness,
        Next, Next1, Next2, vars
<1> QED
    BY <1>1, <1>2, PTL

--------------------------------------------------------------------------------
(* Liveness properties. *)


LIndInv ==
    /\ IndInv
    /\ (pc1 = 1) => (c1 = 1)
    /\ (pc2 = 1) => (c2 = 1)
    /\ (pc1 = 8) => (turn = 2)
    /\ (pc2 = 8) => (turn = 1)
    /\ (pc1 \in {6, 7, 8}) => (pc2 \notin {6, 7, 8})
    /\ (pc2 \in {6, 7, 8}) => (pc1 \notin {6, 7, 8})


LSys ==
    /\ LIndInv /\ [][Next]_vars
    /\ WF_vars1(pc1 # 9 /\ Next1)
    /\ WF_vars2(pc2 # 9 /\ Next2)


THEOREM LIndInvIsInductive ==
    Sys => []LIndInv
PROOF
<1>1. ASSUME Init
      PROVE LIndInv
    BY <1>1 DEF Init, LIndInv, IndInv
<1>2. ASSUME LIndInv /\ [Next]_vars
      PROVE LIndInv'
    BY <1>2 DEF LIndInv, IndInv, Next, Next1, Next2, vars
<1> QED
    BY <1>1, <1>2, PTL DEF Sys


IndInv2 ==
    /\ IndInv
    /\ (pc1 = 1) => (c1 = 1)
    /\ (pc2 = 1) => (c2 = 1)

LInv ==
    /\ \/ turn = 1
       \/ turn = 2

    /\ (turn = 1) => ~ (turn = 2)
    /\ (turn = 2) => ~ (turn = 1)

    /\ \/ pc1 = 1
       \/ pc1 = 2
       \/ pc1 = 3
       \/ pc1 = 4
       \/ pc1 = 5
       \/ pc1 = 6
       \/ pc1 = 7
       \/ pc1 = 8
       \/ pc1 = 9

    /\ \/ c1 = 0 /\ ~ (c1 = 1)
       \/ ~ (c1 = 0) /\ c1 = 1

    /\ (pc1 = 1) => (c1 = 1)
    /\ (pc1 = 2) => (c1 = 0)
    /\ (pc1 = 3) => (c1 = 0)
    /\ (pc1 = 4) => (c1 = 0)
    /\ (pc1 = 5) => (c1 = 1)
    /\ (pc1 = 6) => (c1 = 0)
    /\ (pc1 = 7) => (c1 = 0)
    /\ (pc1 = 8) => (c1 = 0)
    /\ (pc1 = 9) => (c1 = 1)

    /\ \/ pc2 = 1
       \/ pc2 = 2
       \/ pc2 = 3
       \/ pc2 = 4
       \/ pc2 = 5
       \/ pc2 = 6
       \/ pc2 = 7
       \/ pc2 = 8
       \/ pc2 = 9

    /\ \/ c2 = 0 /\ ~ (c2 = 1)
       \/ ~ (c2 = 0) /\ (c2 = 1)

    /\ (pc2 = 1) => (c2 = 1)
    /\ (pc2 = 2) => (c2 = 0)
    /\ (pc2 = 3) => (c2 = 0)
    /\ (pc2 = 4) => (c2 = 0)
    /\ (pc2 = 5) => (c2 = 1)
    /\ (pc2 = 6) => (c2 = 0)
    /\ (pc2 = 7) => (c2 = 0)
    /\ (pc2 = 8) => (c2 = 0)
    /\ (pc2 = 9) => (c2 = 1)

Trans1 ==
    /\ \/ ~ (pc1 = 1)
       \/ (pc1 = 2)'
       \/ (pc1 = 1)'

    /\ \/ ~ (pc1 = 2)
       \/ (pc1 = 3)'
       \/ (pc1 = 6)'
       \/ (pc1 = 2)'

    /\ \/ ~ (pc1 = 2)
       \/ /\ (c2 = 1) => ~ (pc1 = 3)'
          /\ (c2 = 0) => ~ (pc1 = 6)'

    /\ \/ ~ (pc1 = 3)
       \/ (pc1 = 2)'
       \/ (pc1 = 4)'
       \/ (pc1 = 3)'

    /\ \/ ~ (pc1 = 3)
       \/ /\ (turn = 2) => ~ (pc1 = 2)'
          /\ (turn = 1) => ~ (pc1 = 4)'

    /\ \/ ~ (pc1 = 4)
       \/ (pc1 = 5)'
       \/ (pc1 = 4)'

    /\ \/ ~ (pc1 = 5)
       \/ (pc1 = 1)'
       \/ (pc1 = 5)'

    /\ \/ ~ (pc1 = 5)
       \/ (turn = 2) => ~ (pc1 = 1)'

    /\ \/ ~ (pc1 = 6)
       \/ (pc1 = 7)'
       \/ (pc1 = 6)'

    /\ \/ ~ (pc1 = 7)
       \/ (pc1 = 8)'
       \/ (pc1 = 7)'

    /\ \/ ~ (pc1 = 8)
       \/ (pc1 = 9)'
       \/ (pc1 = 8)'

    /\ \/ ~ (pc1 = 9)
       \/ (pc1 = 1)'
       \/ (pc1 = 9)'

Trans2 ==
    /\ \/ ~ (pc2 = 1)
       \/ (pc2 = 2)'
       \/ (pc2 = 1)'

    /\ \/ ~ (pc2 = 2)
       \/ (pc2 = 3)'
       \/ (pc2 = 6)'
       \/ (pc2 = 2)'

    /\ \/ ~ (pc2 = 2)
       \/ /\ (c1 = 1) => ~ (pc2 = 3)'
          /\ (c1 = 0) => ~ (pc2 = 6)'

    /\ \/ ~ (pc2 = 3)
       \/ (pc2 = 2)'
       \/ (pc2 = 4)'
       \/ (pc2 = 3)'

    /\ \/ ~ (pc2 = 3)
       \/ /\ (turn = 1) => ~ (pc2 = 2)'
          /\ (turn = 2) => ~ (pc2 = 4)'

    /\ \/ ~ (pc2 = 4)
       \/ (pc2 = 5)'
       \/ (pc2 = 4)'

    /\ \/ ~ (pc2 = 5)
       \/ (pc2 = 1)'
       \/ (pc2 = 5)'

    /\ \/ ~ (pc2 = 5)
       \/ (turn = 1) => ~ (pc2 = 1)'

    /\ \/ ~ (pc2 = 6)
       \/ (pc2 = 7)'
       \/ (pc2 = 6)'

    /\ \/ ~ (pc2 = 7)
       \/ (pc2 = 8)'
       \/ (pc2 = 7)'

    /\ \/ ~ (pc2 = 8)
       \/ (pc2 = 9)'
       \/ (pc2 = 8)'

    /\ \/ ~ (pc2 = 9)
       \/ (pc2 = 1)'
       \/ (pc2 = 9)'


THEOREM StarvationFreedom ==
    Sys => /\ StFr1
           /\ StFr2
PROOF
<1>1. \/ ~ Sys
      \/ /\ []IndInv2
         /\ [][Next]_vars
    <2>1. Sys => []IndInv2
        <3>1. ASSUME Init
              PROVE IndInv2
            BY <3>1 DEF Init, IndInv2, IndInv
        <3>2. ASSUME IndInv2 /\ [Next]_vars
              PROVE IndInv2'
            BY <3>2 DEF IndInv2, IndInv, Next, Next1, Next2, vars
        <3> QED
            BY <3>1, <3>2, PTL DEF Sys
    <2>2. Sys => [][Next]_vars
        BY PTL DEF Sys
    <2> QED
        BY <2>1, <2>2
<1>2. ASSUME IndInv2 /\ [Next]_vars
      PROVE Trans1 /\ Trans2
    BY <1>2 DEF IndInv2, IndInv, Next, Next1, Next2, vars,
        Trans1, Trans2
<1>3. Sys => []LInv
    <2>1. ASSUME Init
          PROVE LInv
        BY <2>1 DEF Init, LInv
    <2>2. ASSUME LInv /\ [Next]_vars
          PROVE LInv'
        BY <2>2 DEF LInv, Next, Next1, Next2, vars
    <2> QED
        BY <2>1, <2>2, PTL DEF Sys
<1>4. \/ ~ Sys
      \/ /\ (pc1 = 1) ~> ~ (pc1 = 1)
         /\ (pc1 = 2) ~> ~ (pc1 = 2)
         /\ (pc1 = 3) ~> ~ (pc1 = 3)
         /\ (pc1 = 4) ~> ~ (pc1 = 4)
         /\ (pc1 = 5 /\ turn = 1) ~> ~ (pc1 = 5)
         /\ (pc1 = 6) ~> ~ (pc1 = 6)
         /\ (pc1 = 7) ~> ~ (pc1 = 7)
         /\ (pc1 = 8) ~> ~ (pc1 = 8)

         /\ (pc2 = 1) ~> ~ (pc2 = 1)
         /\ (pc2 = 2) ~> ~ (pc2 = 2)
         /\ (pc2 = 3) ~> ~ (pc2 = 3)
         /\ (pc2 = 4) ~> ~ (pc2 = 4)
         /\ (pc2 = 5 /\ turn = 2) ~> ~ (pc2 = 5)
         /\ (pc2 = 6) ~> ~ (pc2 = 6)
         /\ (pc2 = 7) ~> ~ (pc2 = 7)
         /\ (pc2 = 8) ~> ~ (pc2 = 8)
    <2>1. \/ ~ Sys
          \/ /\ (pc1 = 1) ~> ~ (pc1 = 1)
             /\ (pc1 = 2) ~> ~ (pc1 = 2)
             /\ (pc1 = 3) ~> ~ (pc1 = 3)
             /\ (pc1 = 4) ~> ~ (pc1 = 4)
             /\ (pc1 = 5 /\ turn = 1) ~> ~ (pc1 = 5)
             /\ (pc1 = 6) ~> ~ (pc1 = 6)
             /\ (pc1 = 7) ~> ~ (pc1 = 7)
             /\ (pc1 = 8) ~> ~ (pc1 = 8)
        <3>1. \/ ~ Sys
              \/ (pc1 = 1) ~> ~ (pc1 = 1)
            <4>1. ASSUME IndInv2 /\ (pc1 = 1)
                  PROVE ENABLED <<pc1 # 9 /\ Next1>>_vars1
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next1, vars1
            <4>2. ASSUME /\ pc1 = 1
                         /\ <<pc1 # 9 /\ Next1>>_vars1
                  PROVE (pc1 = 2)'
                BY <4>2 DEF Next1, vars1
            <4>3. ASSUME pc1 = 2
                  PROVE ~ (pc1 = 1)
                BY <4>3
            <4> QED
                BY <4>1, <4>2, <4>3, <1>1, PTL DEF Sys
        <3>2. \/ ~ Sys
              \/ (pc1 = 2) ~> ~ (pc1 = 2)
            <4>1. ASSUME IndInv2 /\ (pc1 = 2)
                  PROVE ENABLED <<pc1 # 9 /\ Next1>>_vars1
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next1, vars1
            <4>2. ASSUME /\ pc1 = 2
                         /\ <<pc1 # 9 /\ Next1>>_vars1
                  PROVE \/ (pc1 = 3)'
                        \/ (pc1 = 6)'
                BY <4>2 DEF Next1, vars1
            <4>3. ASSUME \/ pc1 = 3
                         \/ pc1 = 6
                  PROVE ~ (pc1 = 2)
                BY <4>3
            <4> QED
                BY <4>1, <4>2, <4>3, <1>1, PTL DEF Sys
        <3>3. \/ ~ Sys
              \/ (pc1 = 3) ~> ~ (pc1 = 3)
            <4>1. ASSUME IndInv2 /\ (pc1 = 3)
                  PROVE ENABLED <<pc1 # 9 /\ Next1>>_vars1
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next1, vars1
            <4>2. ASSUME /\ pc1 = 3
                         /\ <<pc1 # 9 /\ Next1>>_vars1
                  PROVE \/ (pc1 = 2)'
                        \/ (pc1 = 4)'
                BY <4>2 DEF Next1, vars1
            <4>3. ASSUME \/ pc1 = 2
                         \/ pc1 = 4
                  PROVE ~ (pc1 = 3)
                BY <4>3
            <4> QED
                BY <4>1, <4>2, <4>3, <1>1, PTL DEF Sys
        <3>4. \/ ~ Sys
              \/ (pc1 = 4) ~> ~ (pc1 = 4)
            <4>1. ASSUME IndInv2 /\ (pc1 = 4)
                  PROVE ENABLED <<pc1 # 9 /\ Next1>>_vars1
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next1, vars1
            <4>2. ASSUME /\ pc1 = 4
                         /\ <<pc1 # 9 /\ Next1>>_vars1
                  PROVE (pc1 = 5)'
                BY <4>2 DEF Next1, vars1
            <4>3. ASSUME pc1 = 5
                  PROVE ~ (pc1 = 4)
                BY <4>3
            <4> QED
                BY <4>1, <4>2, <4>3, <1>1, PTL DEF Sys
        <3>5. \/ ~ Sys
              \/ (pc1 = 5 /\ turn = 1) ~> ~ (pc1 = 5)
            <4>1. ASSUME IndInv2 /\ (pc1 = 5 /\ turn = 1)
                  PROVE ENABLED <<pc1 # 9 /\ Next1>>_vars1
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next1, vars1
            <4>2. ASSUME /\ IndInv2 /\ [Next]_vars
                         /\ pc1 = 5 /\ turn = 1
                  PROVE (turn = 1)'
                BY <4>2 DEF IndInv2, IndInv, Next, Next1, Next2, vars
            <4>3. ASSUME /\ pc1 = 5
                         /\ <<pc1 # 9 /\ Next1>>_vars1
                  PROVE (pc1 = 1)'
                BY <4>3 DEF Next1, vars1
            <4>4. ASSUME pc1 = 1
                  PROVE ~ (pc1 = 5)
                BY <4>4
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4, <1>1, PTL DEF Sys
        <3>6. \/ ~ Sys
              \/ (pc1 = 6) ~> ~ (pc1 = 6)
            <4>1. ASSUME IndInv2 /\ (pc1 = 6)
                  PROVE ENABLED <<pc1 # 9 /\ Next1>>_vars1
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next1, vars1
            <4>2. ASSUME /\ pc1 = 6
                         /\ <<pc1 # 9 /\ Next1>>_vars1
                  PROVE (pc1 = 7)'
                BY <4>2 DEF Next1, vars1
            <4>3. ASSUME pc1 = 7
                  PROVE ~ (pc1 = 6)
                BY <4>3
            <4> QED
                BY <4>1, <4>2, <4>3, <1>1, PTL DEF Sys
        <3>7. \/ ~ Sys
              \/ (pc1 = 7) ~> ~ (pc1 = 7)
            <4>1. ASSUME IndInv2 /\ (pc1 = 7)
                  PROVE ENABLED <<pc1 # 9 /\ Next1>>_vars1
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next1, vars1
            <4>2. ASSUME /\ pc1 = 7
                         /\ <<pc1 # 9 /\ Next1>>_vars1
                  PROVE (pc1 = 8)'
                BY <4>2 DEF Next1, vars1
            <4>3. ASSUME pc1 = 8
                  PROVE ~ (pc1 = 7)
                BY <4>3
            <4> QED
                BY <4>1, <4>2, <4>3, <1>1, PTL DEF Sys
        <3>8. \/ ~ Sys
              \/ (pc1 = 8) ~> ~ (pc1 = 8)
            <4>1. ASSUME IndInv2 /\ (pc1 = 8)
                  PROVE ENABLED <<pc1 # 9 /\ Next1>>_vars1
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next1, vars1
            <4>2. ASSUME /\ pc1 = 8
                         /\ <<pc1 # 9 /\ Next1>>_vars1
                  PROVE (pc1 = 9)'
                BY <4>2 DEF Next1, vars1
            <4>3. ASSUME pc1 = 9
                  PROVE ~ (pc1 = 8)
                BY <4>3
            <4> QED
                BY <4>1, <4>2, <4>3, <1>1, PTL DEF Sys
        <3> QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8
    <2>2. \/ ~ Sys
          \/ /\ (pc2 = 1) ~> ~ (pc2 = 1)
             /\ (pc2 = 2) ~> ~ (pc2 = 2)
             /\ (pc2 = 3) ~> ~ (pc2 = 3)
             /\ (pc2 = 4) ~> ~ (pc2 = 4)
             /\ (pc2 = 5 /\ turn = 2) ~> ~ (pc2 = 5)
             /\ (pc2 = 6) ~> ~ (pc2 = 6)
             /\ (pc2 = 7) ~> ~ (pc2 = 7)
             /\ (pc2 = 8) ~> ~ (pc2 = 8)
        <3>1. \/ ~ Sys
              \/ (pc2 = 1) ~> ~ (pc2 = 1)
            <4>1. ASSUME IndInv2 /\ (pc2 = 1)
                  PROVE ENABLED <<pc2 # 9 /\ Next2>>_vars2
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next2, vars2
            <4>2. ASSUME /\ pc2 = 1
                         /\ <<pc2 # 9 /\ Next2>>_vars2
                  PROVE (pc2 = 2)'
                BY <4>2 DEF Next2, vars2
            <4>3. ASSUME pc2 = 2
                  PROVE ~ (pc2 = 1)
                BY <4>3
            <4> QED
                BY <4>1, <4>2, <4>3, <1>1, PTL DEF Sys
        <3>2. \/ ~ Sys
              \/ (pc2 = 2) ~> ~ (pc2 = 2)
            <4>1. ASSUME IndInv2 /\ (pc2 = 2)
                  PROVE ENABLED <<pc2 # 9 /\ Next2>>_vars2
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next2, vars2
            <4>2. ASSUME /\ pc2 = 2
                         /\ <<pc2 # 9 /\ Next2>>_vars2
                  PROVE \/ (pc2 = 3)'
                        \/ (pc2 = 6)'
                BY <4>2 DEF Next2, vars2
            <4>3. ASSUME \/ pc2 = 3
                         \/ pc2 = 6
                  PROVE ~ (pc2 = 2)
                BY <4>3
            <4> QED
                BY <4>1, <4>2, <4>3, <1>1, PTL DEF Sys
        <3>3. \/ ~ Sys
              \/ (pc2 = 3) ~> ~ (pc2 = 3)
            <4>1. ASSUME IndInv2 /\ (pc2 = 3)
                  PROVE ENABLED <<pc2 # 9 /\ Next2>>_vars2
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next2, vars2
            <4>2. ASSUME /\ pc2 = 3
                         /\ <<pc2 # 9 /\ Next2>>_vars2
                  PROVE \/ (pc2 = 2)'
                        \/ (pc2 = 4)'
                BY <4>2 DEF Next2, vars2
            <4>3. ASSUME \/ pc2 = 2
                         \/ pc2 = 4
                  PROVE ~ (pc2 = 3)
                BY <4>3
            <4> QED
                BY <4>1, <4>2, <4>3, <1>1, PTL DEF Sys
        <3>4. \/ ~ Sys
              \/ (pc2 = 4) ~> ~ (pc2 = 4)
            <4>1. ASSUME IndInv2 /\ (pc2 = 4)
                  PROVE ENABLED <<pc2 # 9 /\ Next2>>_vars2
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next2, vars2
            <4>2. ASSUME /\ pc2 = 4
                         /\ <<pc2 # 9 /\ Next2>>_vars2
                  PROVE (pc2 = 5)'
                BY <4>2 DEF Next2, vars2
            <4>3. ASSUME pc2 = 5
                  PROVE ~ (pc2 = 4)
                BY <4>3
            <4> QED
                BY <4>1, <4>2, <4>3, <1>1, PTL DEF Sys
        <3>5. \/ ~ Sys
              \/ (pc2 = 5 /\ turn = 2) ~> ~ (pc2 = 5)
            <4>1. ASSUME IndInv2 /\ (pc2 = 5 /\ turn = 2)
                  PROVE ENABLED <<pc2 # 9 /\ Next2>>_vars2
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next2, vars2
            <4>2. ASSUME /\ IndInv2 /\ [Next]_vars
                         /\ pc2 = 5 /\ turn = 2
                  PROVE (turn = 2)'
                BY <4>2 DEF IndInv2, IndInv, Next, Next1, Next2, vars
            <4>3. ASSUME /\ pc2 = 5
                         /\ <<pc2 # 9 /\ Next2>>_vars2
                  PROVE (pc2 = 1)'
                BY <4>3 DEF Next2, vars2
            <4>4. ASSUME pc2 = 1
                  PROVE ~ (pc2 = 5)
                BY <4>4
            <4> QED
                BY <4>1, <4>2, <4>3, <4>4, <1>1, PTL DEF Sys
        <3>6. \/ ~ Sys
              \/ (pc2 = 6) ~> ~ (pc2 = 6)
            <4>1. ASSUME IndInv2 /\ (pc2 = 6)
                  PROVE ENABLED <<pc2 # 9 /\ Next2>>_vars2
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next2, vars2
            <4>2. ASSUME /\ pc2 = 6
                         /\ <<pc2 # 9 /\ Next2>>_vars2
                  PROVE (pc2 = 7)'
                BY <4>2 DEF Next2, vars2
            <4>3. ASSUME pc2 = 7
                  PROVE ~ (pc2 = 6)
                BY <4>3
            <4> QED
                BY <4>1, <4>2, <4>3, <1>1, PTL DEF Sys
        <3>7. \/ ~ Sys
              \/ (pc2 = 7) ~> ~ (pc2 = 7)
            <4>1. ASSUME IndInv2 /\ (pc2 = 7)
                  PROVE ENABLED <<pc2 # 9 /\ Next2>>_vars2
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next2, vars2
            <4>2. ASSUME /\ pc2 = 7
                         /\ <<pc2 # 9 /\ Next2>>_vars2
                  PROVE (pc2 = 8)'
                BY <4>2 DEF Next2, vars2
            <4>3. ASSUME pc2 = 8
                  PROVE ~ (pc2 = 7)
                BY <4>3
            <4> QED
                BY <4>1, <4>2, <4>3, <1>1, PTL DEF Sys
        <3>8. \/ ~ Sys
              \/ (pc2 = 8) ~> ~ (pc2 = 8)
            <4>1. ASSUME IndInv2 /\ (pc2 = 8)
                  PROVE ENABLED <<pc2 # 9 /\ Next2>>_vars2
                BY <4>1, ExpandENABLED DEF IndInv2, IndInv, Next2, vars2
            <4>2. ASSUME /\ pc2 = 8
                         /\ <<pc2 # 9 /\ Next2>>_vars2
                  PROVE (pc2 = 9)'
                BY <4>2 DEF Next2, vars2
            <4>3. ASSUME pc2 = 9
                  PROVE ~ (pc2 = 8)
                BY <4>3
            <4> QED
                BY <4>1, <4>2, <4>3, <1>1, PTL DEF Sys
        <3> QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8
    <2> QED
        BY <2>1, <2>2, PTL
<1>5. \/ ~ Sys
      \/ (pc1 = 2 /\ turn = 1) ~> (pc1 = 6)
    <2>1. ASSUME /\ IndInv2 /\ [Next]_vars
                 /\ ~ (pc1 = 6) /\ ~ (pc1 = 6)'
                 /\ \/ pc1 = 2
                    \/ pc1 = 3
                 /\ turn = 1

          PROVE /\ \/ (pc1 = 2)'
                   \/ (pc1 = 3)'
                /\ (turn = 1)'
                /\ (c1 = 0)'
                /\ (c1 = 0)
        BY <2>1 DEF IndInv2, IndInv, Next, Next1, Next2, vars
    <2>2. \/ ~ Sys
          \/ (pc1 = 2 /\ turn = 1) ~> \/ (pc1 = 6)
                                      \/ [](c2 = 1)
        <3>1. \/ ~ Sys
              \/ []((pc1 = 2 /\ turn = 1) =>
                    \/ <> (pc1 = 6)
                    \/ [](turn = 1 /\ c1 = 0))
            BY <1>1, <2>1, PTL
        <3>2. \/ ~ Sys
              \/ ~ <>[](turn = 1 /\ c1 = 0)
              \/ <>[](c2 = 1)
            BY <1>1, <1>2, <1>3, <1>4,
                PTL DEF Trans2, LInv
        <3> QED
            BY <3>1, <3>2, PTL
    <2>3. \/ ~ Sys
          \/ (pc1 = 2 /\ turn = 1) ~> \/ (pc1 = 6)
                                      \/ []<>(pc1 = 2)
        BY <1>1, <1>4, <2>1, PTL DEF Trans1
    <2>4. ASSUME /\ IndInv2 /\ [Next]_vars
                  /\ pc1 = 2
           PROVE \/ (pc1 = 2)'
                 \/ c2 = 0 /\ (pc1 = 3)'
                 \/ (pc1 = 6)'
        BY <2>4 DEF IndInv2, IndInv, Next, Next1, Next2, vars
    <2>5. ~ (c2 = 0) \/ ~ (c2 = 1)
        OBVIOUS
    <2>6. \/ ~ Sys
          \/ (<>[](c2 = 1) /\ []<>(pc1 = 2)) ~> (pc1 = 6)
        BY <1>1, <1>4, <2>4, <2>5, PTL
    <2> QED
        BY <2>2, <2>3, <2>6, PTL
<1>6. \/ ~ Sys
      \/ (pc2 = 2 /\ turn = 2) ~> (pc2 = 6)
    (* The proof of step <1>6 is adapted from a copy of the
    proof of step <1>5.
    *)
    <2>1. ASSUME /\ IndInv2 /\ [Next]_vars
                 /\ ~ (pc2 = 6) /\ ~ (pc2 = 6)'
                 /\ \/ pc2 = 2
                    \/ pc2 = 3
                 /\ turn = 2

          PROVE /\ \/ (pc2 = 2)'
                   \/ (pc2 = 3)'
                /\ (turn = 2)'
                /\ (c2 = 0)'
                /\ (c2 = 0)
        BY <2>1 DEF IndInv2, IndInv, Next, Next1, Next2, vars
    <2>2. \/ ~ Sys
          \/ (pc2 = 2 /\ turn = 2) ~> \/ (pc2 = 6)
                                      \/ [](c1 = 1)
        <3>1. \/ ~ Sys
              \/ []((pc2 = 2 /\ turn = 2) =>
                    \/ <> (pc2 = 6)
                    \/ [](turn = 2 /\ c2 = 0))
            BY <1>1, <2>1, PTL
        <3>2. \/ ~ Sys
              \/ ~ <>[](turn = 2 /\ c2 = 0)
              \/ <>[](c1 = 1)
            BY <1>1, <1>2, <1>3, <1>4,
                PTL DEF Trans1, LInv
        <3> QED
            BY <3>1, <3>2, PTL
    <2>3. \/ ~ Sys
          \/ (pc2 = 2 /\ turn = 2) ~> \/ (pc2 = 6)
                                      \/ []<>(pc2 = 2)
        BY <1>1, <1>4, <2>1, PTL DEF Trans2
    <2>4. ASSUME /\ IndInv2 /\ [Next]_vars
                 /\ pc2 = 2
           PROVE \/ (pc2 = 2)'
                 \/ c1 = 0 /\ (pc2 = 3)'
                 \/ (pc2 = 6)'
        BY <2>4 DEF IndInv2, IndInv, Next, Next1, Next2, vars
    <2>5. ~ (c1 = 0) \/ ~ (c1 = 1)
        OBVIOUS
    <2>6. \/ ~ Sys
          \/ (<>[](c1 = 1) /\ []<>(pc2 = 2)) ~> (pc2 = 6)
        BY <1>1, <1>4, <2>4, <2>5, PTL
    <2> QED
        BY <2>2, <2>3, <2>6, PTL
<1>7. \/ ~ Sys
      \/ (pc1 = 2 /\ turn = 2) ~> (pc1 = 6)
    <2>1. Sys => []LIndInv
        BY LIndInvIsInductive
    <2>2. \/ ~ Sys
          \/ []((turn = 2) => \/ [](pc2 = 9)
                              \/ <> (turn = 2 /\ ~ (pc2 = 9)))
        <3>1. ASSUME /\ IndInv2 /\ [Next]_vars
                     /\ turn = 2 /\ pc2 = 9
              PROVE (turn = 2)'
            BY <3>1 DEF IndInv2, IndInv, Next, Next1, Next2, vars
        <3> QED
            BY <3>1, <1>1, <1>2, PTL
    <2>3. \/ ~ Sys
          \/ (turn = 2 /\ ~ (pc2 = 9))
                           ~> \/ pc2 = 6
                              \/ pc2 = 7
                              \/ (pc2 = 2 /\ turn = 2)
        <3>1. ASSUME IndInv2 /\ [Next]_vars
              PROVE \/ pc2 = 1 \/ pc2 = 2 \/ pc2 = 3
                    \/ pc2 = 4 \/ pc2 = 5 \/ pc2 = 6
                    \/ pc2 = 7 \/ pc2 = 8 \/ pc2 = 9
            BY <3>1 DEF IndInv2, IndInv, Next, Next1, Next2, vars
        <3>2. ASSUME /\ IndInv2 /\ [Next]_vars
                     /\ turn = 2
                     /\ \/ pc2 = 1 \/ pc2 = 2 \/ pc2 = 3
                        \/ pc2 = 4 \/ pc2 = 5
              PROVE (turn = 2)'
            BY <3>2 DEF IndInv2, IndInv, Next, Next1, Next2, vars
        <3>3. ASSUME /\ LIndInv
                     /\ turn = 2
              PROVE ~ (pc2 = 8)
            BY <3>3 DEF LIndInv, IndInv
        <3> QED
            BY <3>1, <3>2, <3>3, <2>1, <1>1, <1>2, <1>4, PTL DEF Trans2
    <2>4. \/ ~ Sys
          \/ (pc2 = 6 \/ pc2 = 7) ~> (turn = 1)
        <3>1. ASSUME /\ IndInv2 /\ [Next]_vars
                     /\ pc2 = 7
              PROVE
                    \/ (pc2 = 7)'
                    \/ (turn = 1)'
            BY <3>1 DEF IndInv2, IndInv, Next, Next1, Next2, vars
        <3> QED
            BY <1>1, <1>2, <1>4, <3>1, PTL DEF Trans2
    <2>5. \/ ~ Sys
          \/ []((turn = 2) => \/ [](pc2 = 9)
                              \/ <>(turn = 1))
        BY <2>2, <2>3, <1>6, <2>4, PTL
    <2>6. \/ ~ Sys
          \/ []((turn = 2) => \/ [](c2 = 1)
                              \/ <>(turn = 1))
        BY <1>3, <2>5, PTL DEF LInv
    <2>7. \/ ~ Sys
          \/ (pc1 = 2 /\ turn = 2) ~>
                \/ pc1 = 6
                \/ pc1 = 2 /\ turn = 1
        <3>1. ASSUME /\ IndInv2 /\ [Next]_vars
                     /\ \/ pc1 = 1
                        \/ pc1 = 2
                        \/ pc1 = 3
                        \/ pc1 = 4
                        \/ pc1 = 5
                     /\ turn = 1
              PROVE /\ (turn = 1)'
            BY <3>1 DEF IndInv2, IndInv, Next, Next1, Next2, vars
        <3> QED
            BY <1>1, <1>2, <1>4, <2>6, <3>1, PTL DEF Trans1
    <2> QED
        BY <2>7, <1>5, PTL
<1>8. \/ ~ Sys
      \/ (pc2 = 2 /\ turn = 1) ~> (pc2 = 6)
    (* The proof of step <1>8 is adapted from a copy of the
    proof of step <1>7.
    *)
    <2>1. Sys => []LIndInv
        BY LIndInvIsInductive
    <2>2. \/ ~ Sys
          \/ []((turn = 1) => \/ [](pc1 = 9)
                              \/ <> (turn = 1 /\ ~ (pc1 = 9)))
        <3>1. ASSUME /\ IndInv2 /\ [Next]_vars
                     /\ turn = 1 /\ pc1 = 9
              PROVE (turn = 1)'
            BY <3>1 DEF IndInv2, IndInv, Next, Next1, Next2, vars
        <3> QED
            BY <3>1, <1>1, <1>2, PTL
    <2>3. \/ ~ Sys
          \/ (turn = 1 /\ ~ (pc1 = 9))
                           ~> \/ pc1 = 6
                              \/ pc1 = 7
                              \/ (pc1 = 2 /\ turn = 1)
        <3>1. ASSUME IndInv2 /\ [Next]_vars
              PROVE \/ pc1 = 1 \/ pc1 = 2 \/ pc1 = 3
                    \/ pc1 = 4 \/ pc1 = 5 \/ pc1 = 6
                    \/ pc1 = 7 \/ pc1 = 8 \/ pc1 = 9
            BY <3>1 DEF IndInv2, IndInv, Next, Next1, Next2, vars
        <3>2. ASSUME /\ IndInv2 /\ [Next]_vars
                     /\ turn = 1
                     /\ \/ pc1 = 1 \/ pc1 = 2 \/ pc1 = 3
                        \/ pc1 = 4 \/ pc1 = 5
              PROVE (turn = 1)'
            BY <3>2 DEF IndInv2, IndInv, Next, Next1, Next2, vars
        <3>3. ASSUME /\ LIndInv
                     /\ turn = 1
              PROVE ~ (pc1 = 8)
            BY <3>3 DEF LIndInv, IndInv
        <3> QED
            BY <3>1, <3>2, <3>3, <2>1, <1>1, <1>2, <1>4, PTL DEF Trans1
    <2>4. \/ ~ Sys
          \/ (pc1 = 6 \/ pc1 = 7) ~> (turn = 2)
        <3>1. ASSUME /\ IndInv2 /\ [Next]_vars
                     /\ pc1 = 7
              PROVE
                    \/ (pc1 = 7)'
                    \/ (turn = 2)'
            BY <3>1 DEF IndInv2, IndInv, Next, Next1, Next2, vars
        <3> QED
            BY <1>1, <1>2, <1>4, <3>1, PTL DEF Trans1
    <2>5. \/ ~ Sys
          \/ []((turn = 1) => \/ [](pc1 = 9)
                              \/ <>(turn = 2))
        BY <2>2, <2>3, <1>5, <2>4, PTL
    <2>6. \/ ~ Sys
          \/ []((turn = 1) => \/ [](c1 = 1)
                              \/ <>(turn = 2))
        BY <1>3, <2>5, PTL DEF LInv
    <2>7. \/ ~ Sys
          \/ (pc2 = 2 /\ turn = 1) ~>
                \/ pc2 = 6
                \/ pc2 = 2 /\ turn = 2
        <3>1. ASSUME /\ IndInv2 /\ [Next]_vars
                     /\ \/ pc2 = 1
                        \/ pc2 = 2
                        \/ pc2 = 3
                        \/ pc2 = 4
                        \/ pc2 = 5
                     /\ turn = 2
              PROVE /\ (turn = 2)'
            BY <3>1 DEF IndInv2, IndInv, Next, Next1, Next2, vars
        <3> QED
            BY <1>1, <1>2, <1>4, <2>6, <3>1, PTL DEF Trans2
    <2> QED
        BY <2>7, <1>6, PTL
<1> QED
    BY <1>3, <1>5, <1>6, <1>7, <1>8, PTL DEF StFr1, StFr2, LInv

================================================================================
