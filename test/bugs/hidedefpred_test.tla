---- MODULE hidedefpred_test ----

EXTENDS TLAPS

C == TRUE
HIDE DEF C

(** The following result might be solved if C is given the type bool.
    This must not happen, as C's defn is hidden.
*)
THEOREM C = TRUE \/ C = FALSE
    OBVIOUS

====
stderr: status:failed
