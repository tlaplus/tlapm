(** Helpers for working with [TL.Proof.T.usable]. *)

module TL := Tlapm_lib

val empty : TL.Proof.T.usable
val add_steps : TL.Proof.T.stepno list -> TL.Proof.T.usable -> TL.Proof.T.usable

val add_defs :
  TL.Proof.T.use_def TL.Property.wrapped list ->
  TL.Proof.T.usable ->
  TL.Proof.T.usable

val add_defs_str : string list -> TL.Proof.T.usable -> TL.Proof.T.usable

val add_defs_from_pf :
  TL.Proof.T.proof -> TL.Proof.T.usable -> TL.Proof.T.usable

val add_to_pf : TL.Proof.T.proof -> TL.Proof.T.usable -> TL.Proof.T.proof
(** Merge usable into an existing proof. *)
