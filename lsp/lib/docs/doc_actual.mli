(** Actual state of the document. *)

open Util
open Prover
open Prover.ToolboxProtocol

type t

val make : LspT.DocumentUri.t -> Doc_vsn.t -> t option -> t
val vsn : t -> int
val text : t -> string
val proof_res : t -> Doc_proof_res.t
val locate_proof_range : t -> TlapmRange.t -> TlapmRange.t
val get_obligation_state : t -> TlapmRange.Position.t -> Proof_step.t option

(* TODO: Rename all the following: prover_obl ... *)
val prepare_proof : t -> int -> t option
val add_obl : t -> int -> tlapm_obligation -> t option
val add_notif : t -> int -> tlapm_notif -> t option
val terminated : t -> int -> t option
