---------------------- MODULE FunctionDefinitionBoundeds -----------------------
(* Test that function definitions allow bounded declarations.

Bounded declarations can include tuple declarations.
*)
f[x \in {TRUE}, y \in TRUE] == x

g[x \in {TRUE}, <<y, z>> \in TRUE \X FALSE] == x /\ (y \/ ~ z)
================================================================================
