---- MODULE test_case ----

THEOREM CASE TRUE -> TRUE
OBVIOUS

CONSTANT x, A, B, C

THEOREM
  ASSUME x = 1,
         1 # 2,
         A
  PROVE CASE x = 1 -> A
          [] x = 2 -> B
  OBVIOUS

THEOREM
  ASSUME x = 1,
         1 # 2,
         A
  PROVE CASE x = 1 -> A
          [] x = 2 -> B
          [] OTHER -> C
  OBVIOUS

====
