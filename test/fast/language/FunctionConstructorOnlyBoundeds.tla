-------------------- MODULE FunctionConstructorOnlyBoundeds --------------------
(* Test that function constructors allow only bounded declarations. *)
f == [x \in TRUE, y |-> TRUE]
================================================================================
stderr: Error: Could not parse
