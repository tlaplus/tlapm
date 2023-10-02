type t

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
end

val create :
  Eio.Switch.t ->
  Eio__.Fs.dir_ty Eio.Path.t ->
  Eio_unix.Process.mgr_ty Eio.Process.mgr ->
  ToolboxProtocol.tlapm_msg Eio.Stream.t ->
  Tlapm_lsp_docs.t ->
  t

val start_async :
  t -> Tlapm_lsp_docs.tk -> int -> int -> int -> (t, string) result
