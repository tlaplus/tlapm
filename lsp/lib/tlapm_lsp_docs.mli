(** Here we maintain a list of documents and their revisions. *)

module OblMap : Map.S with type key = int
open Tlapm_lsp_prover.ToolboxProtocol

type t
(** A document store type. *)

type tk = Lsp.Types.DocumentUri.t
(** Key type to identify documents. *)

type tv = {
  text : string;
  version : int;
  in_use : bool;
  proof_ref : int;
  obligations : tlapm_obligation OblMap.t;
}
(** Info on a single revision of a document. *)

val empty : t
(** Create new empty document store. *)

val add : t -> tk -> int -> string -> t
(** Either add document or its revision. Forgets all previous unused revisions. *)

val rem : t -> tk -> t
(** Remove a document with all its revisions. *)

val get_opt : t -> tk -> (string * int) option
(** Lookup document's last revision. *)

val get_vsn_opt : t -> tk -> int -> string option
(** Lookup specific document revision. *)

val with_doc_vsn : t -> tk -> int -> (tv -> tv * 'a) -> 'a option * t
(** Execute action on a specific version of a document. *)

val next_p_ref_opt : t -> tk -> int -> t * (int * string) option
(** Increment the prover ref for the specified doc/vsn. *)
