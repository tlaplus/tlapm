---- MODULE box_closure_sequent_mixed_context_test ----
EXTENDS TLAPS

Fid(a) == a

\* c is rigid and x is flexible.
\* Both assumptions of the inner sequent are
\* diamond-closed, so the sequent is box-closed.

THEOREM
    ASSUME NEW CONSTANT c,
           NEW VARIABLE x,
           ASSUME c = 0, Fid(<>(x = 0)) PROVE FALSE
    PROVE []((c = 0 /\ Fid(<>(x = 0))) => FALSE)
BY PTL

============================================================================
known: the inner sequent stays unboxed, so LS4 reports the boxed goal false. This already fails at 5c644d20.
