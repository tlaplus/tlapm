---- MODULE noteqfalse_test ----

EXTENDS TLAPS

(** 'x \/ ~ x' is a theorem of TLA+, but 'x = TRUE \/ x = FALSE' is
    inconsistent, because it would imply that BOOLEAN is the set of all sets.
    Thus the theorem below cannot be true.
*)

THEOREM ASSUME NEW x
        PROVE ~ x => x = FALSE
    OBVIOUS

====
