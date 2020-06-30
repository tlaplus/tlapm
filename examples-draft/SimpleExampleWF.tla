---------------------------- MODULE SimpleExampleWF ----------------------------
(* An example that involves WF and induction over temporal properties. *)
EXTENDS Integers, NaturalsInduction, TLAPS


VARIABLE x


Init == x = 0
Next == x' = x + 1

Spec == Init /\ [][Next]_x /\ WF_x(Next)


THEOREM
    \A n \in Nat:  Spec => <>(x = n)
PROOF
(* Type invariance. *)
<1> DEFINE Inv == x \in Nat
<1>1. Spec => []Inv
    <2>1. Init => Inv
        BY DEF Init, Inv
    <2>2. Inv /\ [Next]_x => Inv'
        BY DEF Inv, Next
    <2> QED
        BY <2>1, <2>2, PTL DEF Spec
(* Temporal property over which induction is applied. *)
<1> DEFINE P(m) == Spec => <>(x = m)
<1> HIDE DEF P
(* Induction over natural numbers. *)
<1>2. \A n \in Nat:  P(n)
    (* Base case for induction. *)
    <2>1. P(0)
        BY PTL DEF P, Spec, Init
    (* Inductive case. *)
    <2>2. \A n \in Nat:  P(n) => P(n + 1)
        <3>1. SUFFICES
                ASSUME NEW n \in Nat
                PROVE (Spec /\ <>(x = n)) => <>(x = n + 1)
            BY <3>1 DEF P
        (* If x reaches n then it remains n or increases by 1. *)
        <3>2. Spec => [] \/ ~ (x = n)
                         \/ <> \/ [] (x = n)
                               \/ (x = n + 1)
            <4>1. ASSUME Inv /\ [Next]_x
                  PROVE  \/ ~ (x = n)
                         \/ (x = n)'
                         \/ (x = n + 1)'
                BY <4>1 DEF Inv, Next
            <4> QED
                BY <1>1, <4>1, PTL DEF Spec
        (* Spec implies infinitely many Next steps that change x. *)
        <3>3. Spec => []<><<Next>>_x
            (* Replacing ENABLED by quantifiers. *)
            <4>1. ASSUME Inv
                  PROVE ENABLED <<Next>>_x
                BY <4>1, ExpandENABLED DEF Next, Inv
            (* Enabledness and fairness imply liveness. *)
            <4>2. ASSUME []Inv
                  PROVE WF_x(Next) => []<><<Next>>_x
                BY <4>1, <4>2, PTL
            <4> QED
                BY <1>1, <4>1, <4>2 DEF Spec
        (* Any <<Next>>_x step when x = n changes x so that ~(x = n)'. *)
        <3>4. ASSUME Inv /\ (x = n) /\ <<Next>>_x
              PROVE ~(x = n)'
            BY <3>4 DEF Inv, Next
        <3> QED
            BY <1>1, <3>2, <3>3, <3>4, PTL
    <2> QED
        BY <2>1, <2>2, NatInduction
(* Unhiding the definition of operator P. *)
<1> QED
    BY <1>2 DEF P


================================================================================
