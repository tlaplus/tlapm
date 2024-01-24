(** Maintains the proof progress in the client app. Here we use the
    server initiated progress and cancellation support, because the
    VSCode don't support the client-initiated workDoneProgress
    with LSP. *)

(* TODO:

   Terminal OBL states:
       @!!status:trivial

       @!!status:proved

       @!!status:failed
       @!!prover:isabelle
*)

module LspT := Lsp.Types

type t

val make : unit -> t
(** Create new instance of progress tracker. *)

module type Callbacks = sig
  type t

  val next_req_id : t -> Jsonrpc.Id.t * t
  val lsp_send : t -> Jsonrpc.Packet.t -> t
end

module Make (CB : Callbacks) : sig
  val is_latest : t -> LspT.ProgressToken.t -> bool
  (** Checks if the token is of the last progress.  *)

  val proof_started : t -> int -> CB.t -> t * CB.t
  (** Called when new TLAPM run is initiated. *)

  val obl_num : t -> int -> int -> CB.t -> t * CB.t
  (** Called when a number of obligations is received from the TLAPM. *)

  val obl_changed : t -> int -> int -> CB.t -> t * CB.t
  (** Called when some proof obligation state change is received from TLAPM. *)

  val proof_ended : t -> int -> CB.t -> t * CB.t
  (** Called when the TLAPM terminates. *)
end
