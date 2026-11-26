------------------- MODULE box_closure_sequent_test -------------------

\* <>(x = 0) is diamond-closed and [](y = 0) is box-closed, so
\* <>(x = 0) => [](y = 0) implies its own box.  If <>(x = 0) holds in a
\* later state, it held at the start, and [](y = 0) still holds there.
\* The sequent spelling and the identity around the diamond must stay
\* provable: coalescing Fid(<>(x = 0)) hides the diamond, and PTL then
\* needs the sequent boxed.

EXTENDS TLAPS

VARIABLES x, y

Fid(a) == a

THEOREM (<>(x = 0) => [](y = 0)) => [](<>(x = 0) => [](y = 0))
BY PTL

THEOREM ASSUME ASSUME <>(x = 0) PROVE [](y = 0)
         PROVE [](<>(x = 0) => [](y = 0))
BY PTL

THEOREM ASSUME ASSUME Fid(<>(x = 0)) PROVE [](y = 0)
         PROVE [](Fid(<>(x = 0)) => [](y = 0))
BY PTL

=============================================================================
