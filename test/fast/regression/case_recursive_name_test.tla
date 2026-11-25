---- MODULE case_recursive_name_test ----

EXTENDS TLAPS

\* Recursive declarations retain their source names, but the frontend rejects
\* them before a matching name could capture a generated CASE oracle.
RECURSIVE TLA__Anon_case_choice_2_1_Idv(_, _, _, _)

THEOREM Check == (CASE TRUE -> TRUE [] TRUE -> FALSE) \in BOOLEAN
BY SMT

====
result: 3
stderr: Recursive operator definitions are not supported
nostderr: status:proved
