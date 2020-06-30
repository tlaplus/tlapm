(*
 * Copyright (C) 2011-2019  INRIA and Microsoft Corporation
 *)

(* params.ml *)
type t =
  | Isabelle of float * string
  | Zenon of float
  | SmtT of float
  | YicesT of float
  | Z3T of float
  | Cooper
  | Fail   (* FIXME remove ? *)
  | Cvc3T of float
  | LS4 of float
  | Smt2lib of float
  | Smt2z3 of float
  | Smt3 of float
  | Z33 of float
  | Cvc33 of float
  | Yices3 of float
  | Verit of float
  | Spass of float
  | Tptp of float
  | ExpandENABLED
  | ExpandCdot
  | AutoUSE
  | Lambdify
  | ENABLEDaxioms
  | LevelComparison
  | Trivial
;;

(* expr/fmt.ml *)
val pp_print_method : Format.formatter -> t -> unit;;

(* backend/isabelle.ml *)
val prover_meth_of_tac : t -> string option * string option;;

(* backend/prep.ml *)
val timeout : t -> float;;
val scale_time : t -> float -> t;;
val pp_print_tactic : Format.formatter -> t -> unit;;

(* *)
val default_zenon_timeout : float;;
val default_ls4_timeout : float;;
val default_isabelle_timeout : float;;
val default_isabelle_tactic : string;;
val default_yices_timeout : float;;
val default_z3_timeout : float;;
val default_cvc3_timeout : float;;
val default_smt_timeout : float;;
val default_smt2_timeout : float;;
val default_spass_timeout : float;;
val default_tptp_timeout :float;;

val is_temporal : t -> bool;;

type result =
  | Proved of string
  | Failed of string
  | Timedout
  | Interrupted
  | NotTried of string
;;
