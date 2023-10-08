type t

module TlapmRange : sig
  type t

  val as_lsp_range : t -> Lsp.Types.Range.t
  val of_lsp_range : Lsp.Types.Range.t -> t
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

  type tlapm_msg =
    | TlapmWarning of { msg : string }
    | TlapmError of { url : string; msg : string }
    | TlapmObligationsNumber of int
    | TlapmObligation of {
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
  Tlapm_lsp_docs.tk ->
  int ->
  string ->
  TlapmRange.t ->
  (ToolboxProtocol.tlapm_msg -> unit) ->
  ?tlapm_locator:(unit -> (string, string) result) ->
  unit ->
  (t, string) result
(** Start new proof process after canceling the existing processes. *)
