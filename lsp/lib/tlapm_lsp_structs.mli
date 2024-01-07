module LspT = Lsp.Types

module Location : sig
  type t = { uri : LspT.DocumentUri.t; range : LspT.Range.t }

  val make : uri:LspT.DocumentUri.t -> range:LspT.Range.t -> t
  val yojson_of_t : t -> Yojson.Safe.t
end

module TlapsProofObligationResult : sig
  type t = {
    prover : string;
    meth : string;
    status : string;
    duration : int;
    obligation : string option;
  }

  val make :
    prover:string ->
    meth:string ->
    status:string ->
    duration:int ->
    obligation:string option ->
    t

  val yojson_of_t : t -> Yojson.Safe.t
end

module TlapsProofObligationState : sig
  type t = {
    location : Location.t;
    obligation : string;
    results : TlapsProofObligationResult.t list;
  }

  val make :
    location:Location.t ->
    obligation:string ->
    results:TlapsProofObligationResult.t list ->
    t

  val yojson_of_t : t option -> Yojson.Safe.t
  val to_jsonrpc_packet : t option -> Jsonrpc.Packet.t
end
