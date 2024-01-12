(** Here we maintain a list of documents and their revisions. *)

open Tlapm_lsp_prover.ToolboxProtocol
open Tlapm_lsp_prover

module Proof_step : sig
  type t

  val yojson_of_t : t -> Yojson.Safe.t option
end

type t
(** A document store type. *)

type tk = Lsp.Types.DocumentUri.t
(** Key type to identify documents. *)

(** Result of an update, returns an actual list of obligations and errors. *)
module Doc_proof_res : sig
  type t = {
    p_ref : int;
    obs : tlapm_obligation list;
    nts : tlapm_notif list;
    pss : Proof_step.t list;
  }

  val empty : t
  val obs_done : t -> int
end

val empty : t
(** Create new empty document store. *)

val add : t -> tk -> int -> string -> t
(** Either add document or its revision. Forgets all previous unused revisions. *)

val rem : t -> tk -> t
(** Remove a document with all its revisions. *)

val prepare_proof :
  t ->
  tk ->
  int ->
  TlapmRange.t ->
  t * (int * string * TlapmRange.t * Doc_proof_res.t) option
(** Increment the prover ref for the specified doc/vsn. *)

val suggest_proof_range :
  t -> tk -> TlapmRange.t -> t * (int * TlapmRange.t) option
(** Suggest proof range based on the user selection. *)

val add_obl :
  t -> tk -> int -> int -> tlapm_obligation -> t * Doc_proof_res.t option
(** Record obligation for the document, clear all the intersecting ones. *)

val add_notif :
  t -> tk -> int -> int -> tlapm_notif -> t * Doc_proof_res.t option
(** Record obligation for the document, clear all the intersecting ones. *)

val terminated : t -> tk -> int -> int -> t * Doc_proof_res.t option
(** Cleanup the incomplete proof states on termination of the prover. *)

val get_proof_res : t -> tk -> int -> t * Doc_proof_res.t option
(** Get the latest actual proof results. Cleanup them, if needed. *)

val get_proof_res_latest : t -> tk -> t * int option * Doc_proof_res.t option
(** Get the latest actual proof results. Cleanup them, if needed. *)

val get_obligation_state :
  t ->
  tk ->
  int ->
  TlapmRange.t ->
  t * Tlapm_lsp_structs.TlapsProofObligationState.t option
(** Get the current proof state for the specific obligation. *)

val get_obligation_state_latest :
  t ->
  tk ->
  TlapmRange.t ->
  t * Tlapm_lsp_structs.TlapsProofObligationState.t option
(** Get the current proof state for the specific obligation at the latest version of the document. *)
