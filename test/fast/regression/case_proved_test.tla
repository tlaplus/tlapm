---- MODULE case_proved_test ----

\* Valid CASE obligations that each backend must prove (tlaplus/tlapm#304).
\* A CASE denotes CHOOSE'n among the results of its enabled arms; arms are
\* unordered.  `case_unproved_test` pins the valid obligations a backend
\* does not prove.

EXTENDS TLAPS

\* Mutually exclusive guards select the unique enabled arm.
THEOREM SmtDisjoint ==
  ASSUME NEW x
  PROVE  (CASE x = "a" -> "u" [] x # "a" -> "v") = IF x = "a" THEN "u" ELSE "v"
BY SMT

THEOREM ZenonDisjoint ==
  ASSUME NEW x
  PROVE  (CASE x = "a" -> "u" [] x # "a" -> "v") = IF x = "a" THEN "u" ELSE "v"
BY Zenon

\* The OTHER arm is selected iff no guard holds.
THEOREM SmtOther ==
  ASSUME NEW x, x # "a", x # "b"
  PROVE  (CASE x = "a" -> "u" [] x = "b" -> "v" [] OTHER -> "w") = "w"
BY SMT

THEOREM ZenonOther ==
  ASSUME NEW x, x # "a", x # "b"
  PROVE  (CASE x = "a" -> "u" [] x = "b" -> "v" [] OTHER -> "w") = "w"
BY Zenon

THEOREM IsaOther ==
  ASSUME NEW x, x # "a", x # "b"
  PROVE  (CASE x = "a" -> "u" [] x = "b" -> "v" [] OTHER -> "w") = "w"
BY Isa

\* Overlapping arms that agree on their value determine the CASE.
THEOREM SmtSameValue ==
  ASSUME NEW p, NEW q, p, q
  PROVE  (CASE p -> "u" [] q -> "u" [] OTHER -> "w") = "u"
BY SMT

THEOREM ZenonSameValue ==
  ASSUME NEW p, NEW q, p, q
  PROVE  (CASE p -> "u" [] q -> "u" [] OTHER -> "w") = "u"
BY Zenon

THEOREM IsaSameValue ==
  ASSUME NEW p, NEW q, p, q
  PROVE  (CASE p -> "u" [] q -> "u" [] OTHER -> "w") = "u"
BY Isa

\* With overlapping arms, the value is one of the enabled results.
THEOREM SmtMember == (CASE TRUE -> "u" [] TRUE -> "v") \in {"u", "v"}
BY SMT

THEOREM ZenonMember == (CASE TRUE -> "u" [] TRUE -> "v") \in {"u", "v"}
BY Zenon

\* Likewise for a CASE in a hypothesis.
THEOREM SmtHyp ==
  ASSUME NEW p, NEW q, p, q, NEW r, r = (CASE p -> "u" [] q -> "v")
  PROVE  r \in {"u", "v"}
BY SMT

THEOREM ZenonHyp ==
  ASSUME NEW p, NEW q, p, q, NEW r, r = (CASE p -> "u" [] q -> "v")
  PROVE  r \in {"u", "v"}
BY Zenon

\* CASEs with the same set of enabled results are equal, whatever their
\* number of arms: here the third arm repeats the first.
\* `case_unproved_test` has the SMT and Zenon counterparts.
THEOREM IsaArity ==
  ASSUME NEW p, NEW q
  PROVE  (CASE p -> "u" [] q -> "v") = (CASE p -> "u" [] q -> "v" [] p -> "u")
BY Isa

\* Isabelle needs a case split on the guards; `case_unproved_test` shows
\* that it does not find the proof on its own.
THEOREM IsaPermuteSplit ==
  ASSUME NEW p, NEW q, NEW x, NEW y, NEW z
  PROVE  (CASE p -> x [] q -> y [] OTHER -> z) = (CASE q -> y [] p -> x [] OTHER -> z)
<1>1. CASE p /\ q
  BY <1>1, Isa
<1>2. CASE p /\ ~q
  BY <1>2, Isa
<1>3. CASE ~p /\ q
  BY <1>3, Isa
<1>4. CASE ~p /\ ~q
  BY <1>4, Isa
<1> QED
  BY <1>1, <1>2, <1>3, <1>4

====
