(** Here we maintain a list of documents and their revisions. *)

type t
(** A document store type. *)

type tk = Lsp.Types.DocumentUri.t
(** Key type to identify documents. *)

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
