------------------- MODULE SetConstructorsTupleDeclarations --------------------
(* Test that tuple declarations can appear in set constructors. *)
a == {x /\ y:  <<x, y>> \in TRUE \X FALSE}
b == {x /\ y /\ z:  <<x, y>> \in TRUE \X FALSE, z \in TRUE}

c == {<<x, y>> \in TRUE \X FALSE:  x /\ y}
================================================================================
