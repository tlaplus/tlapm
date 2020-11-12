---------------------------- MODULE SimpleExampleWF ----------------------------
(* An example that involves WF and induction over temporal properties. *)
EXTENDS Integers, NaturalsInduction, TLAPS


VARIABLE x  (* The declaration of a variable named x. *)


Init == x = 0  (* The initial condition asserts that x starts equal to 0. *)
Next == x' = x + 1  (* The action Next asserts that x is incremented by 1. *)

Spec == Init /\ [][Next]_x /\ WF_x(Next)  (* The temporal formula Spec asserts
    that variable x starts equal to 0, each step either leaves x unchanged or
    increments x by 1, and whenever a step that increments x and changes x
    remains possible, such a step eventually occurs. *)


THEOREM
    \A n \in Nat:  Spec => <>(x = n)
PROOF
(* Type invariance. *)
<1> DEFINE Inv == x \in Nat  (* The type invariant asserts that x is a natual
    number. *)
<1>1. Spec => []Inv  (* Spec implies the type invariant, *)
    <2>1. Init => Inv  (* because the initial condition implies the
            type invariant, and *)
        BY DEF Init, Inv
    <2>2. Inv /\ [Next]_x => Inv'  (* each step that satisfies the action
            [Next]_x and starts from a state that satisfies the type invariant
            leads to a state that satisfies the type invariant.
            In other words, the type invariant is an inductive invariant. *)
        BY DEF Inv, Next
    <2> QED
        BY <2>1, <2>2, PTL DEF Spec
(* Temporal property P over which induction is applied. The formula P(m)
asserts that Spec implies that eventually variable x equals the value m.
In this specification, m is a natural number, and P(m) will be shown to
be valid for every natural number. *)
<1> DEFINE P(m) == Spec => <>(x = m)
<1> HIDE DEF P  (* We hide the definition of P to reduce the complexity visible
    to the back-end solvers. *)
(* Induction over the set of natural numbers. *)
<1>2. \A n \in Nat:  P(n)
    (* Base case for induction. We show that P(0) is TRUE. *)
    <2>1. P(0)
        BY PTL DEF P, Spec, Init
    (* Inductive case. We show that for every natural number, P(n) implies
    P(n + 1). Together with the base case P(0), these assertions are the
    premises for proving that P(n) holds for every natural number n. *)
    <2>2. \A n \in Nat:  P(n) => P(n + 1)
        <3>1. SUFFICES
                ASSUME NEW n \in Nat
                PROVE (Spec /\ <>(x = n)) => <>(x = n + 1)
                (* In this SUFFICES step we prove that it is sufficient to
                prove the implication (Spec /\ <>(x = n)) => <>(x = n + 1)
                for every natural number n, in order to prove the formula
                \A n \in Nat:  P(n) => P(n + 1). This becomes more evident if
                we expand the definition of P in the formula
                \A n \in Nat:  P(n) => P(n + 1), which results in the formula
                \A n \in Nat:  (Spec => <>(x = n)) => (Spec => <>(x = n + 1)).
                *)
            BY <3>1 DEF P
        (* The temporal formula Spec implies that if x reaches n then
        x forever remains n or eventually x increases by 1. We will use this
        assertion, together with weak fairness of action Next to prove that
        always eventually x increases by 1. *)
        <3>2. Spec => [] \/ ~ (x = n)
                         \/ [] (x = n)
                         \/ <> (x = n + 1)
            <4>1. ASSUME Inv /\ [Next]_x
                  PROVE  \/ ~ (x = n)
                         \/ (x = n)'
                         \/ (x = n + 1)'
                    (* The invariant and action [Next]_x imply that starting
                    from a state where x equls n, next either x equals n or
                    x equals n + 1. *)
                BY <4>1 DEF Inv, Next
                (* Using reasoning by the propositional temporal logic prover
                (PTL) and step <4>1, we deduce that formula Spec implies that
                if x reaches n then x either remains indefinitely equal to n
                or eventually increases by 1. *)
            <4> QED
                BY <1>1, <4>1, PTL DEF Spec
        (* Spec implies infinitely many Next steps that change x. *)
        <3>3. Spec => []<><<Next>>_x
            (* From any state that satisfies the type invariant (x \in Nat),
            the action <<Next>>_x is enabled, which means that a step that
            increments x by 1 and changes x is possible. This assertion is
            proved by first converting the expression ENABLED <<Next>>_x
            to the expression \E u:  u = x + 1 /\ u # x by invoking the
            proof directive ExpandENABLED (with the definition of operator Next
            expanded in the BY DEF statement). *)
            <4>1. ASSUME Inv
                  PROVE ENABLED <<Next>>_x
                  (* The proof directive ExpandENABLED replaces ENABLED by
                  rigid existential quantification (\E). *)
                BY <4>1, ExpandENABLED DEF Next, Inv
            (* Enabledness and weak fairness imply liveness. The formula
            WF_x(Next) can be expanded to
            []<>(~ ENABLED <<Next>>_x) \/ []<><<Next>>_x .
            By step <4>1, []Inv implies []ENABLED <<Next>>_x, which implies
            ~ []<> ~ ENABLED <<Next>>_x . Therefore, the conjunction
            []Inv /\ WF_x(Next) implies []<><<Next>>_x .
            *)
            <4>2. ASSUME []Inv
                  PROVE WF_x(Next) => []<><<Next>>_x
                BY <4>1, <4>2, PTL
            (* The temporal formula Spec implies []Inv /\ WF_x(Next),
            so by step <4>2 the formula Spec implies []<><<Next>_x . *)
            <4> QED
                BY <1>1, <4>2 DEF Spec
        (* Any <<Next>>_x step when x = n changes x so that ~(x = n)'.
        We will use this result together with step <3>2 to show that variable x
        does not remain forever equal to n, but x is eventually incremented
        by 1. *)
        <3>4. ASSUME Inv /\ (x = n) /\ <<Next>>_x
              PROVE ~(x = n)'
            BY <3>4 DEF Inv, Next
        <3> QED
            BY <1>1, <3>2, <3>3, <3>4, PTL
    (* Using the premises P(0) and \A n \in Nat:  P(n) => P(n + 1),
    we deduce by the theorem NatInduction that P(n) is valid for every natural
    number n. *)
    <2> QED
        BY <2>1, <2>2, NatInduction
(* Unhiding the definition of operator P. This step proves the theorem
assertion by making visible the definition of P within the assertion of
step <1>2. *)
<1> QED
    BY <1>2 DEF P


================================================================================
