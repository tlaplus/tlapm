---- MODULE testarith ----

(* This is just for checking the Isabelle translations. *)

EXTENDS Reals

THEOREM test ==
  ASSUME NEW x, NEW y
  PROVE /\ x + y = x + y
        /\ x - y = x - y
\*        /\ (- x) = (- x)
        /\ x * y = x * y
\*        /\ x / y = x / y
\*        /\ x \div y = x \div y
\*        /\ x % y = x % y
\*        /\ x ^ y = x ^ y
\*        /\ Infinity = Infinity
        /\ x <= y <=> x <= y
        /\ x < y <=> x < y
        /\ x >= y <=> x >= y
        /\ x > y <=> x > y
\*        /\ x .. y = x .. y
OBVIOUS

====
