---------------------- MODULE FunctionConstructorBoundeds ----------------------
(* Test that function constructors allow bounded declarations. *)
f == [x \in {TRUE}, y \in TRUE |-> x /\ y]
================================================================================
