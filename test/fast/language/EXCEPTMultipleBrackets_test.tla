----------------------- MODULE EXCEPTMultipleBrackets_test ---------------------
(* Test that consecutive brackets and `@` in an `EXCEPT` assignment are
correctly interpreted in the presence of multiple (comma-separated) assignments.
*)
EXTENDS Integers


f == [x \in {1} |-> [y \in {2} |-> 3]]
g == [f EXCEPT ![1][2] = 1]


THEOREM g[1][2] = 1
BY DEF g, f


h == [f EXCEPT ![1][2] = @ + 1]


THEOREM h[1][2] = 4
BY DEF h, f


t == [f EXCEPT ![1][2] = 1, ![1][2] = @ + 1]


THEOREM t[1][2] = 2
BY DEF t, f

================================================================================
