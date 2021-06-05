------------------- MODULE FunctionDefinitionOnlyBoundeds_2 --------------------
(* Test that function definitions allow only bounded declarations.

The below form is a syntax error in TLA+.
Previously, `tlapm` parsed this form.
The syntax error is detected by SANY.
*)
f[x \in TRUE, y] == TRUE
================================================================================
stderr: Error: Could not parse
