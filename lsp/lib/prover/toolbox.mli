(** Parser for the toolbox protocol and all the related data structures. *)

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

(* TODO: This should be removed. *)
val tlapm_obl_state_is_terminal : tlapm_obl_state -> bool

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
    | TlapmObligation of Obligation.t
    | TlapmTerminated
end

(* Parser. *)

type parser_state

val parse_start : parser_state
val parse_line : string -> parser_state -> (Msg.t -> unit) -> parser_state
