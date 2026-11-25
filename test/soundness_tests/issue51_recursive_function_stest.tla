------------- MODULE issue51_recursive_function_stest --------------

\* https://github.com/tlaplus/tlapm/issues/51
\* No function Silly on Nat satisfies Silly[n] = ~Silly[n], so the
\* recursive definition only determines Silly as some CHOOSE value.
\* Proving that Silly equals the defining function literal yields FALSE.
\* The old SMT encoding proved BuggyTheorem by rewriting
\* X = CHOOSE v : P(v) to (\E v : P(v)) => P(X).  The module is the
\* reproducer from the issue.

EXTENDS Naturals, TLAPS

DefSilly(Silly, n) == ~Silly[n]
Silly[n \in Nat] == DefSilly(Silly,n)

THEOREM BuggyTheorem == Silly = [n \in Nat |-> DefSilly(Silly,n)] BY DEF Silly
THEOREM FALSE
  <1> Silly[0] = ~Silly[0] BY BuggyTheorem DEF DefSilly
  <1> QED OBVIOUS

====================================================================
