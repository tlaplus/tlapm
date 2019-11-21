(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(* backend/types.mli *)
type t =
  | Isabelle of string
  | Zenon of zenon
  | Smt
  | Yices
  | Z3
  | Cooper
  | Sorry
and zenon = {
  zenon_timeout : float;
  zenon_fallback : t;
}
;;
type status_type =
  | Trivial
  | BeingProved
  | Success of t
  | Fail of t
  | Checked
  | Interrupted of t
;;

(* fingerprints.ml *)
val pp_print_tactic_fp : Format.formatter -> t -> unit;;
