(*  Copyright 2004 INRIA  *)

open Expr;;

type inductive_arg =
  | Param of string
  | Self
;;

type phrase =
  | Hyp of string * expr * int
  | Def of definition
  | Sig of string * string list * string  (* sym, args, result *)
  | Inductive of
     string * string list * (string * inductive_arg list) list * string
;;

type zphrase =
  | Zhyp of string * expr * int
  | Zdef of definition
  | Zsig of string * string list * string
  | Zinductive of
     string * string list * (string * inductive_arg list) list * string
  | Zinclude of string
;;

val separate :
  string list -> phrase list -> definition list * (expr * int) list
;;

type tpphrase =
  | Include of string * string list option
  | Formula of string * string * expr
  | Annotation of string
;;

val change_to_def : string list -> expr -> definition;;
(** Turn a def-shaped formula into a (real) definition.
    Raise [Invalid_argument] if the argument is not def-shaped. *)
