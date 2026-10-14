---- MODULE case_sharing_test ----

EXTENDS TLAPS

\* CASE lowering binds guards and results locally to avoid duplicating nested
\* expressions.  The bindings must preserve their original variable scopes.

THEOREM SmtNestedGuard ==
  ASSUME NEW p, NEW q, p, ~q
  PROVE
    (CASE (CASE p -> TRUE [] q -> FALSE [] OTHER -> FALSE) -> "yes"
       [] FALSE -> "no"
       [] OTHER -> "other") = "yes"
BY SMT

THEOREM SmtNestedResult ==
  ASSUME NEW p, NEW q
  PROVE
    (CASE TRUE -> (CASE p -> "a" [] q -> "b" [] OTHER -> "c")
       [] TRUE -> "d") \in {"a", "b", "c", "d"}
BY SMT

THEOREM SmtQuantifiedScope ==
  \A x, y :
    /\ (CASE TRUE -> x [] TRUE -> (CASE TRUE -> y [] TRUE -> x))
         \in {x, y}
    /\ (CASE FALSE -> x [] FALSE -> y [] OTHER -> x) = x
BY SMT

THEOREM SmtRepeatedCase ==
  ASSUME NEW p, NEW q, NEW x, NEW y, NEW z, NEW v,
         v = (CASE p -> (CASE q -> x [] TRUE -> y)
                [] TRUE -> z [] OTHER -> x)
  PROVE
    (CASE p -> (CASE q -> x [] TRUE -> y)
       [] TRUE -> z [] OTHER -> x) = v
BY SMT

THEOREM SmtChooseScope ==
  \A x : (CHOOSE y : y = (CASE TRUE -> x [] TRUE -> x)) = x
BY SMT

====
