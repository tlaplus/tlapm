module LspT := Lsp.Types

(** Types representing messages from the prover. *)
module Toolbox : sig
  type tlapm_obl_state =
    | ToBeProved
    | BeingProved
    | Normalized
    | Proved
    | Failed
    | Interrupted
    | Trivial
    | Unknown of string

  val tlapm_obl_state_to_string : tlapm_obl_state -> string

  module Obligation : sig
    type t = {
      id : int;
      loc : Range.t;
      status : tlapm_obl_state;
      fp : string option;
      prover : string option;
      meth : string option;
      reason : string option;
      already : bool option;
      obl : string option;
    }
  end

  type tlapm_notif_severity = TlapmNotifError | TlapmNotifWarning

  type tlapm_notif = {
    loc : Range.t;
    sev : tlapm_notif_severity;
    msg : string;
    url : string option;
  }

  val notif_of_loc_msg : string option -> string -> tlapm_notif

  module Msg : sig
    type t =
      | TlapmNotif of tlapm_notif
      | TlapmObligationsNumber of int
      | TlapmObligationProvers of { id : int; provers : string list }
      | TlapmObligation of Obligation.t
      | TlapmTerminated
  end
end

module Progress : sig
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
    (** Checks if the token is of the last progress. *)

    val proof_started : p_ref:int -> CB.t -> CB.t
    (** Called when new TLAPM run is initiated. *)

    val obl_count : p_ref:int -> obl_count:int -> CB.t -> CB.t
    (** Called when a number of obligations is received from the TLAPM. *)

    val obligation_done : p_ref:int -> obl_id:int -> CB.t -> CB.t
    (** Called when some proof obligation state change is received from TLAPM.
    *)

    val proof_ended : p_ref:int -> CB.t -> CB.t
    (** Called when the TLAPM terminates. *)
  end
end

type t

val create :
  Eio.Switch.t ->
  Eio__.Fs.dir_ty Eio.Path.t ->
  Eio_unix.Process.mgr_ty Eio.Process.mgr ->
  t
(** Create a tlapm process manager. *)

val cancel_all : t -> t
(** Cancel all the ongoing proof processes, await for their termination. *)

val start_async :
  t ->
  LspT.DocumentUri.t ->
  string ->
  Range.t ->
  string list ->
  (Toolbox.Msg.t -> unit) ->
  ?tlapm_locator:(unit -> (string, string) result) ->
  unit ->
  (t, string) result
(** Start new proof process after canceling the existing processes. *)
