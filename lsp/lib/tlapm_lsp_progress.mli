(** Maintains the proof progress in the client app. Here we use the
    server initiated progress and cancellation support, because the
    VSCode don't support the client-initiated workDoneProgress
    with LSP. *)

module type Callbacks = sig
  type t

  val next_req_id : t -> Jsonrpc.Id.t * t
  val lsp_send : t -> Jsonrpc.Packet.t -> t
end

(* TODO: Use it in the Docs. *)
(* TODO: Handle the cancelation. *)
module Make (CB : Callbacks) : sig
  type t

  val make : unit -> t
  (** Create new instance of progress tracker. *)

  val proof_started : t -> int -> CB.t -> t * CB.t
  (** Called when new TLAPM run is initiated. *)

  val obl_num : t -> int -> int -> CB.t -> t * CB.t
  (** Called when a number of obligations is received from the TLAPM. *)

  val obl_progress : t -> int -> int -> CB.t -> t * CB.t
  (** Called when some proof obligation state change is received from TLAPM. *)

  val proof_ended : t -> int -> CB.t -> t * CB.t
  (** Called when the TLAPM terminates. *)
end
