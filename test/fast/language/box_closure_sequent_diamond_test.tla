---- MODULE box_closure_sequent_diamond_test ----
EXTENDS TLAPS

VARIABLE x

Fid(a) == a

\* The inner sequent is ~Fid([](x = 0)).
\* It is diamond-closed.
\* Its negation is therefore box-closed.
\* Fid is intended to exercise operator coalescing.

THEOREM
    ASSUME ASSUME ASSUME Fid([](x = 0)) PROVE FALSE
                  PROVE FALSE
    PROVE [](Fid([](x = 0)))
BY PTL

============================================================================
