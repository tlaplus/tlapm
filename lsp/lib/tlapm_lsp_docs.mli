(** Here we maintain a list of documents and their revisions. *)

open Tlapm_lsp_prover.ToolboxProtocol
open Tlapm_lsp_prover

module PS : sig
  type t

  val yojson_of_t : t -> Yojson.Safe.t option
end

type t
(** A document store type. *)

type tk = Lsp.Types.DocumentUri.t
(** Key type to identify documents. *)

type proof_res = int * tlapm_obligation list * tlapm_notif list * PS.t list
(** Result of an update, returns an actual list of obligations and errors. *)

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
  t * (int * string * TlapmRange.t * proof_res) option
(** Increment the prover ref for the specified doc/vsn. *)

val add_obl : t -> tk -> int -> int -> tlapm_obligation -> t * proof_res option
(** Record obligation for the document, clear all the intersecting ones. *)

val add_notif : t -> tk -> int -> int -> tlapm_notif -> t * proof_res option
(** Record obligation for the document, clear all the intersecting ones. *)

val get_proof_res : t -> tk -> int -> t * proof_res option
(** Get the latest actual proof results. Cleanup them, if needed. *)

val get_proof_res_latest : t -> tk -> t * int option * proof_res option
(** Get the latest actual proof results. Cleanup them, if needed. *)
