type t

module TlapmRange : sig
  type p
  type t

  val as_lsp_range : t -> Lsp.Types.Range.t
  val of_lsp_range : Lsp.Types.Range.t -> t
  val string_of_range : t -> string
  val string_of_pos : p -> string
  val intersects : t -> t -> bool
  val before : p -> t -> bool
  val first_diff_pos : string -> string -> p
end

(** Types representing messages from the prover. *)
module ToolboxProtocol : sig
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

  type tlapm_obligation = {
    id : int;
    loc : TlapmRange.t;
    status : tlapm_obl_state;
    fp : string option;
    prover : string option;
    meth : string option;
    reason : string option;
    already : bool option;
    obl : string option;
  }

  type tlapm_notif_severity = TlapmNotifError | TlapmNotifWarning

  type tlapm_notif = {
    loc : TlapmRange.t;
    sev : tlapm_notif_severity;
    msg : string;
    url : string option;
  }

  type tlapm_msg =
    | TlapmNotif of tlapm_notif
    | TlapmObligationsNumber of int
    | TlapmObligation of tlapm_obligation
    | TlapmTerminated
end

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
  Lsp.Types.DocumentUri.t ->
  int ->
  string ->
  TlapmRange.t ->
  (ToolboxProtocol.tlapm_msg -> unit) ->
  ?tlapm_locator:(unit -> (string, string) result) ->
  unit ->
  (t, string) result
(** Start new proof process after canceling the existing processes. *)
