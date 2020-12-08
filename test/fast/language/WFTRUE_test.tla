---- MODULE WFTRUE_test ----
(* The lexer was not identifying
keywords in fairness subscripts.
For example, WF_TRUE was lexed
as [PUNCT "WF_"; ID "TRUE"],
instead of [PUNCT "WF_"; KWD "TRUE"].
*)

THEOREM WF_TRUE(TRUE) <=> WF_(TRUE)(TRUE)
OBVIOUS

=============================
