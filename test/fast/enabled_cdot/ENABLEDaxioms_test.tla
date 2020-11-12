------------------------- MODULE ENABLEDaxioms_test ----------------------------
(* Unit tests for the implementation of proof rules about `ENABLED`. *)
EXTENDS TLAPS


(* This statement declares three variables. *)
VARIABLE x, y, z


P == x = 1  (* A state predicate. *)
A == x' = 1 /\ y' = 1  (* An action with primed variables. *)
B == z' = 1  (* Another action with primed variables, such that the set of
    primed variables of action A is disjoint from the set of primed variables
    of action B. *)
R == y' = 1 /\ x' = 1  (* An action equivalent to action A. *)

--------------------------------------------------------------------------------
(* Proving that a state predicate can be moved outside the scope of ENABLED,
i.e., that from
    P \in BOOLEAN,
    A \in BOOLEAN,
    ENABLED (P /\ A),
    P is a state predicate
we deduce
    P /\ ENABLED A

The premises P \in BOOLEAN, A \in BOOLEAN, and ENABLED (P /\ A) must appear
as separate proof steps and listed in the BY statement where ENABLEDaxioms
appears. The premise that P is a state predicate is checked automatically by
TLAPS.

If the premises do not appear in this form, then the proof will not
succeed, because TLAPS checks the syntactic form of each premise, including the
levels of the expressions.
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
    (* With the proof directives ExpandENABLED and AutoUSE the expression
    ENABLED (P /\ A) is converted first to ENABLED (P /\ x' = 1 /\ y' = 1) and
    then to (\E u, v:  P /\ u = 1 /\ v = 1), which is equivalent to P,
    so implied by the assumption P (no need to expand the definition of P).
    *)
    BY ExpandENABLED, AutoUSE
<1> QED
    BY <1>1, <1>2, <1>3, ENABLEDaxioms


(* Proving that a state predicate can be moved inside the scope of ENABLED,
i.e., that from
    P \in BOOLEAN,
    A \in BOOLEAN,
    P /\ ENABLED A,
    P is a state predicate
we deduce
    ENABLED (P /\ A)

The premises P \in BOOLEAN, A \in BOOLEAN and P /\ ENABLED A must appear as
separate proof steps and listed in the BY statement where ENABLEDaxioms appears.
The premise that P is a state predicate is checked automatically by TLAPS.

If the premises do not appear in this form, then the proof will not succeed,
because TLAPS checks the syntactic form of each premise, including the levels
of the expressions.
*)
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
        (* AutoUSE expands action A, because it contains primed variables and
        is in the scope of ENABLED, to yield the expression
        ENABLED (x' = 1 /\ y' = 1). ExpandENABLED converts this expression to
        (\E u, v:  u = 1 /\ v = 1), which is valid.
        *)
        BY ExpandENABLED, AutoUSE
    <2> QED
        BY <2>1
<1> QED
    BY <1>1, <1>2, <1>3, ENABLEDaxioms

--------------------------------------------------------------------------------
(* Proving that ENABLED distributes over conjunction for actions with disjoint
sets of primed variables, i.e., that from
    A \in BOOLEAN,
    B \in BOOLEAN,
    ENABLED (A /\ B),
    A and B have disjoint sets of primed variables
we deduce
    (ENABLED A) /\ ENABLED B

The premises A \in BOOLEAN, B \in BOOLEAN, and ENABLED (A /\ B) must appear as
separate proof steps, and listed in the BY statement where ENABLEDaxioms
appears. The premise that A and B have disjoint sets of primed variables is
checked automatically by TLAPS.
*)


THEOREM
    (ENABLED A) /\ ENABLED B
PROOF
<1>1. A \in BOOLEAN
    BY DEF A
<1>2. B \in BOOLEAN
    BY DEF B
<1>3. ENABLED (A /\ B)
    (* The proof directive AutoUSE expands the definitions of operators A and B
    because they are actions in the scope of ENABLED. The result is the
    expression ENABLED (x' = 1 /\ y' = 1 /\ z' = 1). The proof directive
    ExpandENABLED converts this expression to the expression
    (\E u, v, w:  u = 1 /\ v = 1 /\ w = 1).
    *)
    BY ExpandENABLED, AutoUSE
<1> QED
    BY <1>1, <1>2, <1>3, ENABLEDaxioms


(* Proving that ENABLED can be factored out of conjunction for actions with
disjoint sets of primed variables, i.e., that from
    A \in BOOLEAN,
    B \in BOOLEAN,
    (ENABLED A) /\ ENABLED B,
    A and B have disjoint sets of primed variables
we deduce
    ENABLED (A /\ B)

The premises A \in BOOLEAN, B \in BOOLEAN, and (ENABLED A) /\ ENABLED B must
appear as separate proof steps, and listed in the BY statement where
ENABLEDaxioms appears. The premise that A and B have disjoint sets of primed
variables is checked automatically by TLAPS.
*)
THEOREM
    ENABLED (A /\ B)
PROOF
<1>1. A \in BOOLEAN
    BY DEF A
<1>2. B \in BOOLEAN
    BY DEF B
<1>3. (ENABLED A) /\ (ENABLED B)
    (* The proof directive AutoUSE expands the definitions of operators A and B
    because they are actions in the scope of ENABLED. The result is the
    expression (ENABLED (x' = 1 /\ y' = 1)) /\ (ENABLED (z' = 1)).
    The proof directive ExpandENABLED converts this expression to the
    expression (\E u, v:  u = 1 /\ v = 1) /\ (\E w:  w = 1).
    *)
    BY ExpandENABLED, AutoUSE
<1> QED
    BY <1>1, <1>2, <1>3, ENABLEDaxioms

--------------------------------------------------------------------------------

(* This theorem is similar to the previous one, with the difference that P
is a state predicate, instead of an action as A was. So the definition of P
does not contain any primed variables, thus its set of primed variables is
obviously disjoint from the set of primed variables of action B.
*)
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
(* Proving that ENABLED can be factored out of disjunction, i.e., that from
    A \in BOOLEAN,
    B \in BOOLEAN,
    (ENABLED A) \/ ENABLED B
we deduce
    ENABLED (A \/ B)

The premises A \in BOOLEAN, B \in BOOLEAN, and (ENABLED A) \/ ENABLED B must
appear as separate proof steps, and be listed in the BY statement where the
proof directive ENABLEDaxioms appears.
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


(* Proving that ENABLED distributes over the disjunction of actions, i.e., that
from
    A \in BOOLEAN,
    B \in BOOLEAN,
    ENABLED (A \/ B)
we deduce
    (ENABLED A) \/ ENABLED B

The premises A \in BOOLEAN, B \in BOOLEAN, ENABLED (A \/ B) need to appear as
separate proof steps, and be listed in the BY statement where the proof
directive ENABLEDaxioms appears.
*)
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
(* Proving that equality of Boolean-valued actions implies equivalence of
enabledness of these actions, i.e., that from
    A \in BOOLEAN,
    R \in BOOLEAN,
    A = R
we deduce
    (ENABLED A) <=> (ENABLED R)

The premises A \in BOOLEAN, R \in BOOLEAN, and A = R must appear as separate
proof steps, and be listed in the BY statement where the proof directive
ENABLEDaxioms appears.
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
(* Proving that the equivalence of actions implies the equivalence of
enabledness of these actions, i.e., that from
    A <=> R
we deduce
    (ENABLED A) <=> ENABLED R

The premise A <=> R needs to appear as a separate proof step, and be listed in
the BY statement where the proof directive ENABLEDaxioms appears.
*)
THEOREM
    (ENABLED A)  <=>  ENABLED R
PROOF
<1>1. A <=> R
    BY DEF A, R
<1> QED
    BY <1>1, ENABLEDaxioms

--------------------------------------------------------------------------------
(* Proving that the implication of actions implies the implication of the
enabledness of these actions, i.e., that from
    A \in BOOLEAN,
    R \in BOOLEAN,
    A => R
we deduce
    (ENABLED A) => ENABLED R

The premises A \in BOOLEAN, R \in BOOLEAN, and A => R must appear as separate
proof steps, and be listed in the BY statement where the proof directive
ENABLEDaxioms appears.
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
