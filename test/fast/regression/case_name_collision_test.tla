---- MODULE case_name_collision_test ----

EXTENDS TLAPS

\* This user constant has the exact name of the generated two-arm CASE
\* oracle.  Frontend renaming must keep the constant and oracle separate.
\* A collision applies the scalar constant as a four-argument oracle, causing
\* an SMT arity error and a failed proof that the test harness rejects.
CONSTANT TLA__Anon_case_choice_2_1_Idv

THEOREM SmtConstant ==
  (CASE TRUE -> TLA__Anon_case_choice_2_1_Idv [] TRUE -> "other")
    \in {TLA__Anon_case_choice_2_1_Idv, "other"}
BY SMT

====
