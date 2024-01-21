type t

module TlapmRange : sig
  module Position : sig
    type t

    val compare : t -> t -> int
  end

  type t

  val from : t -> Position.t
  val till : t -> Position.t
  val line_from : t -> int
  val line_till : t -> int
  val as_lsp_range : t -> Lsp.Types.Range.t
  val of_lsp_range : Lsp.Types.Range.t -> t
  val of_locus : Tlapm_lib.Loc.locus -> t option
  val of_locus_opt : Tlapm_lib.Loc.locus option -> t option
  val of_locus_must : Tlapm_lib.Loc.locus -> t
  val of_points : Position.t -> Position.t -> t
  val of_all : t
  val join : t -> t -> t
  val string_of_range : t -> string
  val string_of_pos : Position.t -> string
  val compare : t -> t -> int
  val before : Position.t -> t -> bool
  val intersect : t -> t -> bool
  val lines_intersect : t -> t -> bool
  val line_covered : t -> Position.t -> bool
  val lines_covered : t -> t -> bool
  val lines_covered_or_all : t -> t list -> t
  val first_diff_pos : string -> string -> Position.t
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
  val tlapm_obl_state_is_terminal : tlapm_obl_state -> bool

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

  val notif_of_loc_msg : string option -> string -> tlapm_notif

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
