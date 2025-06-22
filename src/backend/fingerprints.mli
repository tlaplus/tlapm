(* Computing fingerprints of proof obligations.

Copyright (C) 2011  INRIA and Microsoft Corporation
*)

(* tlapm.ml *)
val write_fingerprint:
    Proof.T.obligation -> Proof.T.obligation

val fingerprint:
    ?ignore_levels:bool -> Proof.T.obligation -> string
(** Returns a fingerprint for an obligation. By default the levels
    are expected to be assigned to the expressions in the obligation
    and are used when calculating the fingerprint. If [~ignore_levels]
    is set to [true], level information will be ignored. This is
    only added for calculating a hash of an obligation fast enough
    to use it in the LSP server. It must not be used to lookup the
    proof state in the actual proof-checking. *)
