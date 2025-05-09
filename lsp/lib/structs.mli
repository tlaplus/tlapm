(** Extensions to the LSP protocol. *)

module LspT := Lsp.Types

module CountByStepStatus : sig
  type t

  val make :
    proved:int ->
    failed:int ->
    omitted:int ->
    missing:int ->
    pending:int ->
    progress:int ->
    t

  val yojson_of_t : t -> Yojson.Safe.t
end

module TlapsProofObligationNoteLevel : sig
  type t = INFO | WARNING | ERROR

  val level_to_string : t -> string
end

module TlapsProofObligationNote : sig
  type t = { level : TlapsProofObligationNoteLevel.t; text : string }

  val make : level:TlapsProofObligationNoteLevel.t -> text:string -> t
  val yojson_of_t : t -> Yojson.Safe.t
end

module TlapsProofObligationResult : sig
  type t

  val make :
    prover:string ->
    meth:string ->
    status:string ->
    reason:string option ->
    obligation:string option ->
    t

  val yojson_of_t : t -> Yojson.Safe.t
end

module TlapsProofObligationState : sig
  type t

  val make :
    role:string ->
    range:LspT.Range.t ->
    status:string ->
    normalized:string option ->
    notes:TlapsProofObligationNote.t list ->
    results:TlapsProofObligationResult.t list ->
    t

  val yojson_of_t : t -> Yojson.Safe.t
end

module TlapsProofStepDetails : sig
  type t

  val make :
    kind:string ->
    status:string ->
    location:LspT.Location.t ->
    obligations:TlapsProofObligationState.t list ->
    sub_count:CountByStepStatus.t ->
    t

  val yojson_of_t : t option -> Yojson.Safe.t
  val to_jsonrpc_packet : t option -> Jsonrpc.Packet.t
end

(** This is the structure used to create proof step decorators in the client. *)
module TlapsProofStepMarker : sig
  type t

  val make : status:string -> range:LspT.Range.t -> hover:string -> t
  val yojson_of_t : t -> Yojson.Safe.t
end

module InitializationOptions : sig
  type t

  val module_search_paths : t -> string list
  (** Additional paths to use in TLAPS. *)

  val t_of_yojson : Yojson.Safe.t option -> t
end

module ServerCapabilitiesExperimental : sig
  type t

  val make : module_search_paths:string list -> t
  (** Paths proposed by TLAPS for other tools. *)

  val yojson_of_t : t -> Yojson.Safe.t
end
