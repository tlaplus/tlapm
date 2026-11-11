---- MODULE box_closure_sequent_context_test ----
EXTENDS TLAPS

VARIABLE x

Fid(a) == a

\* The declarations introduce rigid constants.
\* The remaining assumptions are diamond-closed.
\* The quantified sequent is box-closed.
\* Rename the bound identifiers in the goal to
\* exercise alpha-equivalence.

THEOREM
    ASSUME ASSUME NEW c,
                  c = 0,
                  NEW d,
                  d = c /\ Fid(<>(x = 0))
           PROVE FALSE
    PROVE [](\A a : a = 0 =>
                (\A b : (b = a /\ Fid(<>(x = 0))) => FALSE))
BY PTL

============================================================================
known: the inner sequent stays unboxed, so LS4 reports the boxed goal false. This already fails at 5c644d20.
