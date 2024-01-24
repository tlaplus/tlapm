(** Actual state of the document. *)

open Util
open Prover

type t

val make : LspT.DocumentUri.t -> Doc_vsn.t -> t option -> t
val vsn : t -> int
val text : t -> string
val proof_res : t -> Doc_proof_res.t
val locate_proof_range : t -> Range.t -> Range.t
val get_obligation_state : t -> Range.Position.t -> Proof_step.t option

(* TODO: Rename all the following: prover_obl ... *)
val prepare_proof : t -> int -> t option
val add_obl : t -> int -> Toolbox.Obligation.t -> t option
val add_notif : t -> int -> Toolbox.tlapm_notif -> t option
val terminated : t -> int -> t option
