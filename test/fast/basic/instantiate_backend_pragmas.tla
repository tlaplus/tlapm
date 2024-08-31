---------------------- MODULE instantiate_backend_pragmas ----------------------
(* Test that references to instantiated backend pragmas work. *)

---------------------------- MODULE BackendPragmas -----------------------------
(* This submodule is used, instead of the module `TLAPS`, to make this test
independent of future changes to the module `TLAPS`.
*)
SMT == TRUE  (*{ by (prover:"smt3") }*)
================================================================================

M == INSTANCE BackendPragmas


THEOREM TRUE
BY M!SMT
================================================================================
