(** Actual state of the document. *)

open Util
open Prover

type t

val make : LspT.DocumentUri.t -> Doc_vsn.t -> t option -> t
val vsn : t -> int
val text : t -> string
val proof_res : t -> Doc_proof_res.t
val locate_proof_range : t -> Range.t -> Range.t
val get_proof_step_details : t -> Range.Position.t -> Proof_step.t option
val prover_prepare : t -> int -> t option
val prover_add_obl : t -> int -> Toolbox.Obligation.t -> t option
val prover_add_notif : t -> int -> Toolbox.tlapm_notif -> t option
val prover_terminated : t -> int -> t option
