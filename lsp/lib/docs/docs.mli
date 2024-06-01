(** Here we maintain a list of documents and their revisions. *)

open Prover
module LspT := Lsp.Types

module Proof_step : sig
  type t
end

module Proof_status : sig
  type t

  val yojson_of_t : t -> Yojson.Safe.t
end

type t
(** A document store type. *)

type parser_fun = Util.parser_fun
(** Parser function to use to parse modules.  *)

type tk = LspT.DocumentUri.t
(** Key type to identify documents. *)

(** Result of an update, returns an actual list of obligations and errors. *)
module Doc_proof_res : sig
  type t

  val make : Toolbox.tlapm_notif list -> Proof_step.t option -> t
  val empty : t
  val as_lsp : t -> LspT.Diagnostic.t list * Structs.TlapsProofStepMarker.t list
end

val empty : parser_fun -> t
(** Create new empty document store. *)

val with_parser : t -> parser_fun -> t
(** Set parser function to use. *)

val add : t -> tk -> int -> string -> t
(** Either add document or its revision. Forgets all previous unused revisions. *)

val rem : t -> tk -> t
(** Remove a document with all its revisions. *)

val suggest_proof_range : t -> tk -> Range.t -> t * (int * Range.t) option
(** Suggest proof range based on the user selection. *)

val prover_prepare :
  t ->
  tk ->
  int ->
  Range.t ->
  p_ref:int ->
  t * (string * Range.t * Doc_proof_res.t) option
(** Increment the prover ref for the specified doc/vsn. *)

val prover_add_obl :
  t -> tk -> int -> int -> Toolbox.Obligation.t -> t * Doc_proof_res.t option
(** Record obligation for the document, clear all the intersecting ones. *)

val prover_add_notif :
  t -> tk -> int -> int -> Toolbox.tlapm_notif -> t * Doc_proof_res.t option
(** Record notification for the document, clear all the intersecting ones. *)

val prover_terminated : t -> tk -> int -> int -> t * Doc_proof_res.t option
(** Cleanup the incomplete proof states on termination of the prover. *)

val get_proof_res : t -> tk -> int -> t * Doc_proof_res.t option
(** Get the latest actual proof results. Cleanup them, if needed. *)

val get_proof_res_latest : t -> tk -> t * int option * Doc_proof_res.t option
(** Get the latest actual proof results. Cleanup them, if needed. *)

val get_proof_step_details :
  t ->
  tk ->
  int ->
  Range.Position.t ->
  t * Structs.TlapsProofStepDetails.t option
(** Get the current proof state for the specific obligation. *)

val get_proof_step_details_latest :
  t -> tk -> Range.Position.t -> t * Structs.TlapsProofStepDetails.t option
(** Get the current proof state for the specific obligation at the latest version of the document. *)
