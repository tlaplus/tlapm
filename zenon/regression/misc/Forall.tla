---- MODULE Forall ----

CONSTANTS i, j, P(_), Q(_)

THEOREM
  ASSUME
    i = j,
    \A i : P(i) => Q(j)
  PROVE
    P(i) => Q(i)
OBVIOUS


====================
