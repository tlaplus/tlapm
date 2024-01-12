(** Actual state of the document. *)

open Util
open Tlapm_lsp_prover
open Tlapm_lsp_prover.ToolboxProtocol

type t

val make : Doc_vsn.t -> t
val vsn : t -> int
val text : t -> string
val merge_into : t -> Doc_vsn.t -> t
val try_parse : t -> LspT.DocumentUri.t -> t
val proof_res : t -> Doc_proof_res.t
val prepare_proof : t -> LspT.DocumentUri.t -> int -> t option
val locate_proof_range : t -> TlapmRange.t -> TlapmRange.t
val get_obligation_state : t -> TlapmRange.t -> Proof_step.t option
val add_obl : t -> int -> tlapm_obligation -> t option
val add_notif : t -> int -> tlapm_notif -> t option
val terminated : t -> int -> t option
