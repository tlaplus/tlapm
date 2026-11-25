---- MODULE case_unproved_test ----

\* Valid CASE obligations (see `case_proved_test`) that a backend does not
\* prove.  This documents incompleteness of TLAPS: ideally every obligation
\* here would be proved.  The test pins current behavior, so each obligation
\* must fail; when a backend starts proving one, move it to
\* `case_proved_test`.  No backend proves on its own that permuting
\* overlapping arms leaves the CASE unchanged, which follows from the
\* extensionality of CHOOSE; Isabelle does with a case split on the guards.
\* The Isabelle timeouts bound the cost of the expected failures.

EXTENDS TLAPS

THEOREM IsaDisjoint ==
  ASSUME NEW x
  PROVE  (CASE x = "a" -> "u" [] x # "a" -> "v") = IF x = "a" THEN "u" ELSE "v"
BY IsaT(2)

THEOREM IsaMember == (CASE TRUE -> "u" [] TRUE -> "v") \in {"u", "v"}
BY IsaT(2)

THEOREM IsaHyp ==
  ASSUME NEW p, NEW q, p, q, NEW r, r = (CASE p -> "u" [] q -> "v")
  PROVE  r \in {"u", "v"}
BY IsaT(2)

\* CASEs with the same set of enabled results are equal, whatever their
\* number of arms; `case_proved_test` has the Isabelle counterpart.
THEOREM SmtArity ==
  ASSUME NEW p, NEW q
  PROVE  (CASE p -> "u" [] q -> "v") = (CASE p -> "u" [] q -> "v" [] p -> "u")
BY SMT

THEOREM ZenonArity ==
  ASSUME NEW p, NEW q
  PROVE  (CASE p -> "u" [] q -> "v") = (CASE p -> "u" [] q -> "v" [] p -> "u")
BY Zenon

THEOREM SmtPermute ==
  ASSUME NEW p, NEW q, NEW x, NEW y, NEW z
  PROVE  (CASE p -> x [] q -> y [] OTHER -> z) = (CASE q -> y [] p -> x [] OTHER -> z)
BY SMT

THEOREM ZenonPermute ==
  ASSUME NEW p, NEW q, NEW x, NEW y, NEW z
  PROVE  (CASE p -> x [] q -> y [] OTHER -> z) = (CASE q -> y [] p -> x [] OTHER -> z)
BY Zenon

THEOREM IsaPermute ==
  ASSUME NEW p, NEW q, NEW x, NEW y, NEW z
  PROVE  (CASE p -> x [] q -> y [] OTHER -> z) = (CASE q -> y [] p -> x [] OTHER -> z)
BY IsaT(2)

====
nostd*: ending abnormally
stderr: 8/16 obligations failed
