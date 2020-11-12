---------------------------- MODULE Enabled_test -------------------------------
(* Unit tests for expanding `ENABLED`. *)
EXTENDS TLAPS


(* This statement declares three variables. *)
VARIABLE x, y, z


P(u) == u'  (* An operator that primes its argument. *)
Q == y  (* An operator that equals an unprimed variable. *)
R == x'  (* An operator that equals a primed variable. *)


(* The proof directive ExpandENABLED translates ENABLED x to x .
The formula x = TRUE implies x, hence x = TRUE implies ENABLED x .
*)
THEOREM
    (x = TRUE)  =>  ENABLED x
PROOF
    BY ExpandENABLED


(* The proof directive ExpandENABLED translates ENABLED (x') to \E u:  u .
The formula \E u:  u is equivalent to TRUE.
*)
THEOREM
    ENABLED (x')
PROOF
    BY ExpandENABLED


(* Reasoning about the expression ENABLED R requires expanding all defined
operators that contain primed variables. The operator R contains the expression
x', which is a primed variable. So we expand R in the BY statement.
The expansion of R happens first, producing the expression ENABLED (x') .
The proof directive ExpandENABLED then translates the expression ENABLED (x')
to \E u:  u .
*)
THEOREM
    ENABLED R
PROOF
    BY ExpandENABLED DEF R


(* Instead of listing R in the statement BY ExpandENABLED DEF R, we can write
the proof directive AutoUSE. This tells TLAPS to expand all defined operators
that need to be expanded in order to reason soundly about ENABLED.
In this case the definition of R contains the expression x', which requires
expansion for ensuring soundness, so R is automatically expanded.
*)
THEOREM
    ENABLED R
PROOF
    BY ExpandENABLED, AutoUSE


(* The expression P(x) expands to x'. This is a primed variable, so P(x) needs
to be expanded before converting the operator ENABLED to existential
quantification. The expansion of P is listed here in the statement
BY ExpandENABLED DEF P and produces the expression ENABLED (x'),
which ExpandENABLED converts to \E u:  u .
*)
THEOREM
    ENABLED P(x)
PROOF
    BY ExpandENABLED DEF P


(* The need to expand the definition of operator P is detected automatically
when using the proof directive AutoUSE. An explicit expansion of P is
unnecessary. The expression ENABLED P(x) is first converted to ENABLED (x'),
and then converted to \E u:  u by the proof directive ExpandENABLED.
*)
THEOREM
    ENABLED P(x)
PROOF
    BY ExpandENABLED, AutoUSE


(* The definition of operator Q contains an unprimed variable, which does not
need to be expanded to soundly reason about ENABLED. So we list only operator
P in the BY DEF statement (because P(x) contains the primed variable x').

The expansion of P happens first, producing the expression ENABLED (x' \/ Q).
This expression is then converted to the expression \E u:  (u \/ Q) by the
proof directive ExpandENABLED.
*)
THEOREM
    ENABLED (P(x) \/ Q)
PROOF
    BY ExpandENABLED DEF P


(* Similarly to the previous example, the definition of operator P needs to be
expanded, unlike the definition of Q, because P(x) contains the primed variable
x' and Q does not contain primed variables. The necessary expansion (of P)
is performed by the proof directive AutoUSE, to yield the expression
ENABLED (x' \/ Q). ExpandENABLED converts this expression to \E u:  (u \/ Q).
*)
THEOREM
    ENABLED (P(x) \/ Q)
PROOF
    BY ExpandENABLED, AutoUSE

--------------------------------------------------------------------------------

Yunprimed == y
F == ENABLED (z' /\ Yunprimed)
G == /\ Yunprimed
     /\ \E zprime:  zprime


(* A proof that expands also Yunprimed, even though this expansion is
unnecessary for ensuring soundness.
*)
THEOREM EnabledEliminationWithUnexpanded ==
    F = G
PROOF
    BY ExpandENABLED DEF F, G, Yunprimed
    (* This proof is sound with the operator Yunprimed expanded or not. *)


(* The definition of operator F needs to be explicitly expanded, so that the
occurrence of the operator ENABLED become visible to the proof directive
ExpandENABLED. The definition of the operator G needs to be expanded to prove
the equivalence.
*)
THEOREM
    F = G
PROOF
    BY ExpandENABLED DEF F, G


--------------------------------------------------------------------------------

(* The operator Yunprimed needs to be expanded in this example to prove the
equivalence. AutoUSE would not do so, because Yunprimed does not contain any
primed variables.
*)
THEOREM
   ASSUME
       NEW A,
       A <=> ENABLED Yunprimed
   PROVE
       A <=> ENABLED (z' /\ y)
PROOF
    BY ExpandENABLED DEF Yunprimed

--------------------------------------------------------------------------------

A == (x \in BOOLEAN) /\ (x' = ~ x)  (* An action. *)
B == ENABLED (x \in BOOLEAN /\ << A >>_x)  (* An ENABLED expression defined
    using the action A. *)
BwithAexpanded ==
    ENABLED /\ x \in BOOLEAN
            /\ x' = ~ x
            /\ x' # x  (* An action that is equivalent to B with the definition
                of action A expanded. *)

(* The definitions of both A and B need to be expanded to prove this
implication.
*)
THEOREM
    A => B
PROOF
    BY ExpandENABLED DEF A, B


(* Listing A and B in the BY DEF statement is still needed in thise case
even if AutoUSE is present, because the occurrence of A as the first argument
to the implication => is not in the scope of an ENABLED, so it would not be
expanded by AutoUSE, and the occurrence of B also is not in the scope of an
ENABLED. The definition of B contains an ENABLED, but this is not a reason for
AutoUSE to expand B.

The proof directive AutoUSE would expand the occurrence of action A within
the definition of B, because it is an action in the scope of ENABLED.
However, this expansion of A is performed due to listing A in the BY DEF
statement, before the proof directive AutoUSE is applied.
*)
THEOREM
    A => B
PROOF
    BY ExpandENABLED, AutoUSE DEF A, B


(* Here the operators B and BwithAexpanded need to be explicitly expanded
to prove the equivalence, and the operator A needs to be expanded to ensure
soundness, because A is an action that occurs within the scope of ENABLED in
the definition of B.
*)
THEOREM
    B <=> BwithAexpanded
PROOF
    BY ExpandENABLED DEF A, B, BwithAexpanded


(* By including the proof directive AutoUSE, the operator A need not be
explicitly expanded. The expansion of A within the definition of B is performed
automatically by the proof directive AutoUSE, and then ExpandENABLED converts
the assertion to (\E u:  x \in BOOLEAN /\ x \in BOOLEAN /\ u = ~ x /\ u # x)
<=> (\E u:  x \in BOOLEAN /\ u = ~ x /\ u # x) .
*)
THEOREM
    B <=> BwithAexpanded
PROOF
    BY ExpandENABLED, AutoUSE DEF B, BwithAexpanded

--------------------------------------------------------------------------------

(* This theorem is proved by applying the proof directive ExpandENABLED,
which converts the assertion to (\E u:  y /\ u) = (\E u:  u /\ y).
*)
THEOREM
    (ENABLED (y /\ x')) = ENABLED (x' /\ y)
PROOF
    BY ExpandENABLED

--------------------------------------------------------------------------------

C == x' = x  (* An operator that expresses that x remains unchanged. *)
D == ENABLED C  (* A state predicate that describes the states from where x
    can remain unchanged. *)


(* The operator D is expanded by listing D in the BY DEF statement, because the
definition of D contains an occurrence of ENABLED. The expansion of D makes the
ENABLED visible to the proof directive AutoUSE, which expands the operator C,
because C is an action that occurs in the scope of ENABLED within the
definition of operator D. After these expansions take place, the proof
directive ExpandENABLED converts the expression ENABLED (x' = x) to the
expression \E u:  (u' = x), which is equivalent to TRUE.
*)
THEOREM
    D
PROOF
    BY ExpandENABLED, AutoUSE DEF D


--------------------------------------------------------------------------------

(* The first ENABLED expression is parsed as (ENABLED y) /\ x', which is
equivalent to y /\ x', which implies ENABLED (y /\ x'), because the latter is
equivalent to \E u:  y /\ u .
*)
THEOREM
    (ENABLED y /\ x') => ENABLED (y /\ x')
PROOF
    BY ExpandENABLED


(* These two ENABLED expressions are equivalent, as proved by applying the
proof directive ExpandENABLED. For this reason, it is useful to include
parentheses around the argument of ENABLED if it is an expression that contains
operators.
*)
THEOREM
    ((ENABLED y) /\ x')  <=>  ENABLED y /\ x'
PROOF
    BY ExpandENABLED

================================================================================
