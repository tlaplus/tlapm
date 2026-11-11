---- MODULE box_closure_sequent_nested_test ----
EXTENDS TLAPS

VARIABLE x

Fid(a) == a

\* Three polarity reversals require the innermost
\* assumption to be diamond-closed.
\* ~Fid(<>(x = 0)) is box-closed.

THEOREM
    ASSUME ASSUME ASSUME ASSUME Fid(<>(x = 0)) PROVE FALSE
                         PROVE FALSE
                  PROVE FALSE
    PROVE [](~Fid(<>(x = 0)))
BY PTL

============================================================================
