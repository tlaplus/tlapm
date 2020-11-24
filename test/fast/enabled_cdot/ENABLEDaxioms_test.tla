------------------------- MODULE ENABLEDaxioms_test ----------------------------
(* Unit tests for the implementation of proof rules about `ENABLED`. *)
EXTENDS TLAPS


VARIABLE x, y, z


P == x = 1
A == x' = 1 /\ y' = 1
B == z' = 1
R == y' = 1 /\ x' = 1

--------------------------------------------------------------------------------
(* Proving


    P,
    P \in BOOLEAN,
    A \in BOOLEAN
|-
    (P /\ ENABLED A) <=> ENABLED (P /\ A)
*)


THEOREM
    ASSUME P
    PROVE P /\ ENABLED A
PROOF
<1>1. P \in BOOLEAN
    BY DEF P
<1>2. A \in BOOLEAN
    BY DEF A
<1>3. ENABLED (P /\ A)
    BY ExpandENABLED, AutoUSE
<1> QED
    BY <1>1, <1>2, <1>3, ENABLEDaxioms


THEOREM
    ASSUME P
    PROVE ENABLED (P /\ A)
PROOF
<1>1. P \in BOOLEAN
    BY DEF P
<1>2. A \in BOOLEAN
    BY DEF A
<1>3. P /\ ENABLED A
    <2>1. ENABLED A
        BY ExpandENABLED, AutoUSE
    <2> QED
        BY <2>1
<1> QED
    BY <1>1, <1>2, <1>3, ENABLEDaxioms

--------------------------------------------------------------------------------
(* Proving


    A \in BOOLEAN,
    B \in BOOLEAN
|-
    ENABLED (A /\ B) <=> (ENABLED A /\ ENABLED B)
*)


THEOREM
    (ENABLED A) /\ ENABLED B
PROOF
<1>1. A \in BOOLEAN
    BY DEF A
<1>2. B \in BOOLEAN
    BY DEF B
<1>3. ENABLED (A /\ B)
    BY ExpandENABLED, AutoUSE
<1> QED
    BY <1>1, <1>2, <1>3, ENABLEDaxioms


THEOREM
    ENABLED (A /\ B)
PROOF
<1>1. A \in BOOLEAN
    BY DEF A
<1>2. B \in BOOLEAN
    BY DEF B
<1>3. (ENABLED A) /\ (ENABLED B)
    BY ExpandENABLED, AutoUSE
<1> QED
    BY <1>1, <1>2, <1>3, ENABLEDaxioms

--------------------------------------------------------------------------------

THEOREM
    ASSUME P
    PROVE ENABLED (P /\ B)
PROOF
<1>1. P \in BOOLEAN
    BY DEF P
<1>2. B \in BOOLEAN
    BY DEF B
<1>3. (ENABLED P) /\ ENABLED B
    <2>1. ENABLED P
        BY ExpandENABLED, AutoUSE
    <2>2. ENABLED B
        BY ExpandENABLED, AutoUSE
    <2> QED
        BY <2>1, <2>2
<1> QED
    BY <1>1, <1>2, <1>3, ENABLEDaxioms

--------------------------------------------------------------------------------
(* Proving


    A \in BOOLEAN,
    B \in BOOLEAN
|-
    ENABLED (A \/ B) <=> (ENABLED A \/ ENABLED B)
*)


THEOREM
    ENABLED (A \/ B)
PROOF
<1>1. A \in BOOLEAN
    BY DEF A
<1>2. B \in BOOLEAN
    BY DEF B
<1>3. (ENABLED A) \/ (ENABLED B)
    <2>1. ENABLED A
        BY ExpandENABLED, AutoUSE
    <2>2. ENABLED B
        BY ExpandENABLED, AutoUSE
    <2> QED
        BY <2>1, <2>2
<1> QED
    BY <1>1, <1>2, <1>3, ENABLEDaxioms


THEOREM
    (ENABLED A) \/ (ENABLED B)
PROOF
<1>1. A \in BOOLEAN
    BY DEF A
<1>2. B \in BOOLEAN
    BY DEF B
<1>3. ENABLED (A \/ B)
    BY ExpandENABLED, AutoUSE
<1> QED
    BY <1>1, <1>2, <1>3, ENABLEDaxioms

--------------------------------------------------------------------------------
(* Proving


    A \in BOOLEAN,
    R \in BOOLEAN,
    A = R
|-
    (ENABLED A) <=> (ENABLED R)
*)


THEOREM
    (ENABLED A) <=> (ENABLED R)
PROOF
<1>1. A \in BOOLEAN
    BY DEF A
<1>2. R \in BOOLEAN
    BY DEF R
<1>3. A = R
    BY DEF A, R
<1> QED
    BY <1>1, <1>2, <1>3, ENABLEDaxioms

--------------------------------------------------------------------------------
(* Proving


    A <=> R
|-
    (ENABLED A) <=> ENABLED R
*)


THEOREM
    (ENABLED A)  <=>  ENABLED R
PROOF
<1>1. A <=> R
    BY DEF A, R
<1> QED
    BY <1>1, ENABLEDaxioms

--------------------------------------------------------------------------------
(* Proving


    A \in BOOLEAN,
    R \in BOOLEAN,
    A => R
|-
    (ENABLED A) => ENABLED R
*)


THEOREM
    (ENABLED A)  =>  ENABLED R
PROOF
<1>1. A \in BOOLEAN
    BY DEF A
<1>2. R \in BOOLEAN
    BY DEF R
<1>3. A => R
    BY DEF A, R
<1> QED
    BY <1>1, <1>2, <1>3, ENABLEDaxioms

================================================================================
