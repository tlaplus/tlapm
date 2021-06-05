------------------- MODULE ExistsNotBothBoundedAndUnbounded --------------------
(* Test that \E does not allow both bounded and unbounded declarations
within the same quantifier.
*)
E == \E x \in TRUE, y:  TRUE
================================================================================
stderr: Error: Could not parse
