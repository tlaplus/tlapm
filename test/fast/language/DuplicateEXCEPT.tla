----------------------------- MODULE DuplicateEXCEPT ---------------------------
(* Test that comma-separated assignments in `EXCEPT` are correctly interpreted.

Multiple assignments in an `EXCEPT` constructor mean nesting of `EXCEPT`
constructors, as defined in [1, page 304].


Reference
=========

[1] Leslie Lamport, Specifying Systems, Addison-Wesley, 2002
*)
EXTENDS Integers


f == [x \in {1} |-> x]


THEOREM [f EXCEPT ![1] = @ + 1, ![1] = @ + 2][1] = 4
BY DEF f


(*
Correctly expanding the left-hand side of the equality in the theorem above
yields:

[[[x \in {1} |-> x] EXCEPT ![1] = [x \in {1} |-> x][1] + 1]
    EXCEPT ![1] = [
        [x \in {1} |-> x] EXCEPT ![1] = [x \in {1} |-> x][1] + 1
        ][1] + 2][1]
*)


================================================================================
