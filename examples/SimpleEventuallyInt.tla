-------------------------- MODULE SimpleEventuallyInt --------------------------
(* How to prove that an integer value will eventually be reached. *)
EXTENDS Integers, NaturalsInduction, TLAPS


VARIABLE x


Init == x = 0
Next == /\ x < 20
        /\ x' = x + 1

System == /\ Init
          /\ [][Next]_x
          /\ WF_x(Next)

Property == <>(x = 20)


THEOREM
    System => Property
PROOF
<1> DEFINE TypeOK == x \in Nat
<1> HIDE DEF TypeOK
<1>1. System => []TypeOK
    <2>1. Init => TypeOK
        BY DEF Init, TypeOK
    <2>2. ASSUME TypeOK /\ [Next]_x
          PROVE TypeOK'
        BY <2>2 DEF TypeOK, Next
    <2> QED
        BY <2>1, <2>2, PTL DEF System
<1> DEFINE
        P(n) == (n <= 20 /\ System) => <>(x = n)
<1> HIDE DEF P
<1>2. \A n \in Nat:  P(n)
    <2>1. P(0)
        BY PTL DEF P, System, Init
    <2>2. ASSUME NEW CONSTANT n, n \in Nat
          PROVE P(n) => P(n + 1)
        <3>1. SUFFICES
                ((n <= 20 /\ System) => <>(x = n))
                => ((n + 1 <= 20 /\ System) => <>(x = n + 1))
            BY <3>1 DEF P
        <3>2. (n + 1 <= 20) => (n < 20 /\ n <= 20)
            BY <2>2
        <3>3. ASSUME TypeOK /\ x < 20
              PROVE ENABLED <<Next>>_x
            BY <2>2, <3>3, ExpandENABLED, AutoUSE DEF TypeOK
        <3>4. ASSUME n < 20 /\ x = n /\ <<Next>>_x
              PROVE (x = n + 1)'
            BY <2>2, <3>4 DEF Next
        <3>5. ASSUME x = n /\ [Next]_x
              PROVE \/ (x = n)'
                    \/ (x = n + 1)'
            BY <2>2, <3>5 DEF Next
        <3>6. ASSUME TypeOK
              PROVE ~ /\ x = n
                      /\ x = n + 1
            BY <2>2, <3>6 DEF TypeOK
        <3>7. (n < 20) => [](n < 20)
            <4>1. (n < 20) => (n < 20)'
                OBVIOUS
            <4> QED
                BY <4>1, PTL
        <3>8. ASSUME n < 20 /\ x = n
              PROVE x < 20
            BY <3>8
        <3> QED
            BY <1>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, PTL DEF System
    <2> QED
        BY <2>1, <2>2, NatInduction, Isa
<1>3. P(20)
    BY <1>2
<1> QED
    BY <1>3 DEF P, Property
================================================================================
