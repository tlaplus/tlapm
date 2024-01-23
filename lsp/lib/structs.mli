(** Extensions to the LSP protocol. *)

module LspT := Lsp.Types

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
    range:LspT.Range.t ->
    normalized:string option ->
    results:TlapsProofObligationResult.t list ->
    t

  val yojson_of_t : t -> Yojson.Safe.t
end

module TlapsProofStepDetails : sig
  type t

  val make :
    kind:string ->
    location:LspT.Location.t ->
    obligations:TlapsProofObligationState.t list ->
    t

  val yojson_of_t : t option -> Yojson.Safe.t
  val to_jsonrpc_packet : t option -> Jsonrpc.Packet.t
end

(** This is the structure used to create proof step decorators in the client. *)
module TlapsProofStateMarker : sig
  type t

  val make : range:LspT.Range.t -> state:string -> hover:string -> t
  val yojson_of_t : t -> Yojson.Safe.t
end
