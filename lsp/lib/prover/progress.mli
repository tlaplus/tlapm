(** Maintains the proof progress in the client app. Here we use the
    server initiated progress and cancellation support, because the
    VSCode don't support the client-initiated workDoneProgress
    with LSP. *)

module LspT := Lsp.Types

type t

module type Callbacks = sig
  type p := t
  type t

  val next_req_id : t -> Jsonrpc.Id.t * t
  val lsp_send : t -> Jsonrpc.Packet.t -> t
  val with_progress : t -> (t -> p -> t * p) -> t
end

module Make (CB : Callbacks) : sig
  val make : unit -> t
  (** Create new instance of progress tracker. *)

  val is_latest : t -> LspT.ProgressToken.t -> bool
  (** Checks if the token is of the last progress.  *)

  val proof_started : p_ref:int -> CB.t -> CB.t
  (** Called when new TLAPM run is initiated. *)

  val obl_count : p_ref:int -> obl_count:int -> CB.t -> CB.t
  (** Called when a number of obligations is received from the TLAPM. *)

  val obligation_done : p_ref:int -> obl_id:int -> CB.t -> CB.t
  (** Called when some proof obligation state change is received from TLAPM. *)

  val proof_ended : p_ref:int -> CB.t -> CB.t
  (** Called when the TLAPM terminates. *)
end
