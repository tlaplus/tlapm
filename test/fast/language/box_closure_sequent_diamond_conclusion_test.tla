---- MODULE box_closure_sequent_diamond_conclusion_test ----
EXTENDS TLAPS

VARIABLES x, y

Fid(a) == a

\* The inner sequent has a box-closed assumption
\* and a diamond-closed conclusion.
\* Therefore the inner sequent is diamond-closed,
\* and its negation is box-closed.

THEOREM
    ASSUME ASSUME ASSUME Fid([](x = 0))
                         PROVE Fid(<>(y = 0))
                  PROVE FALSE
    PROVE [](~(Fid([](x = 0)) => Fid(<>(y = 0))))
BY PTL

============================================================================
