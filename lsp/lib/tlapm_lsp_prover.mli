type t

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

  type tlapm_loc = (int * int) * (int * int)

  val range_of_loc : tlapm_loc -> Lsp.Types.Range.t
  val loc_of_range : Lsp.Types.Range.t -> tlapm_loc

  type tlapm_msg =
    | TlapmWarning of { msg : string }
    | TlapmError of { url : string; msg : string }
    | TlapmObligationsNumber of int
    | TlapmObligation of {
        id : int;
        loc : tlapm_loc;
        status : tlapm_obl_state;
        fp : string option;
        prover : string option;
        meth : string option;
        reason : string option;
        already : bool option;
        obl : string option;
      }
    | TlapmTerminated
end

val create :
  Eio.Switch.t ->
  Eio__.Fs.dir_ty Eio.Path.t ->
  Eio_unix.Process.mgr_ty Eio.Process.mgr ->
  (ToolboxProtocol.tlapm_msg -> unit) ->
  Tlapm_lsp_docs.t ->
  t
(** Create a tlapm process manager. *)

val cancel_all : t -> t
(** Cancel all the ongoing proof processes, await for their termination. *)

val start_async :
  t ->
  Tlapm_lsp_docs.tk ->
  int ->
  int ->
  int ->
  ?tlapm_locator:(unit -> (string, string) result) ->
  unit ->
  (t, string) result
(** Start new proof process after canceling the existing processes. *)
