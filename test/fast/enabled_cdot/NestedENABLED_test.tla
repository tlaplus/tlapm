---------------------- MODULE NestedENABLED_test -------------------------------
(* Unit test of `ENABLED` and `\cdot` occurring in scope of `ENABLED`.

This module tests nesting of `ENABLED` without occurrence of definitions
(so without expansion of definitions by the user or by `AutoUSE`.
*)
EXTENDS TLAPS


(* `\cdot` occurs in scope of `ENABLED` and index depth of `z` is larger
than the number of bounds in the quantifier that replaces `ENABLED`.

This theorem tests the shifting of indices after `Lamda`s have been
introduced and before anonymization of the newly introduced `Lambda`
parameters.


*)
THEOREM
    (* The declarations are in a sequent to ensure that the index of `z`
    remains small, even if this theorem is moved to within the module,
    which otherwise could change the number of theorems in the context,
    thus the depth of declarations in the deque of the context,
    so the indices (thus the value of the `z` index would be above the
    value checked at `Expr.Subst.app_ix` for the first pattern case of
    `Bump`). This pertains to testing the functions
    `Expr.Action.shift_indices_after_lambdify` and
    `Expr.Action.shift_indices`.
    *)
    ASSUME VARIABLE w, VARIABLE x, VARIABLE y, VARIABLE z
    PROVE (z = 0) =>
        ENABLED (
            (z = 0 /\ z' = 1 /\ x' /\ y' /\ w')
            \cdot
            (z = 1 /\ z' = 2))
PROOF
    BY ExpandENABLED, ExpandCdot, Zenon

--------------------------------------------------------------------------------
VARIABLE x, y, z


(* `ENABLED` occurs in scope of `ENABLED`. *)
THEOREM
    ENABLED /\ x'
            /\ ENABLED (y' /\ ENABLED (z'))
            /\ ENABLED (x')
PROOF
    BY ExpandENABLED, Zenon


(* `\cdot` occurs in scope of `ENABLED`. *)
THEOREM
    (x = 0) =>
        ENABLED (
            (x = 0 /\ x' = 1)
            \cdot
            (x = 1 /\ x' = 2))
PROOF
    BY ExpandENABLED, ExpandCdot, Zenon

================================================================================
