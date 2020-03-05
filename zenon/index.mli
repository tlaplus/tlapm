(*  Copyright 2004 INRIA  *)

open Expr;;

(* ==== main formula list ==== *)

(* [add] and [remove] must be used in LIFO order *)
val add : expr -> int -> unit;;
val remove : expr -> unit;;

val member : expr -> bool;;
val get_goalness : expr -> int;;
val get_all : unit -> (expr * goalness) list;;

val find_pos : string -> (expr * goalness) list;;
val find_neg : string -> (expr * goalness) list;;

val find_eq_lr : expr -> expr list;;
val find_eq_rl : expr -> expr list;;

val find_eq : expr -> expr list;;
val find_neq : expr -> expr list;;

val find_eq_str : unit -> (expr * string) list;;
val find_str_eq : unit -> (expr * string) list;;

val is_meta_set : expr -> bool;;

(* ==== transitive relations ==== *)

type direction = Left | Right | Both;;

type head = Sym of string | Tau of expr | Meta of expr;;
val get_head : expr -> head;;
exception No_head;;

val add_trans : expr -> unit;;
val find_trans_left : string -> head -> (expr * goalness) list;;
val find_trans_right : string -> head -> (expr * goalness) list;;

val add_negtrans : expr -> unit;;
val find_negtrans_left : string -> head -> (expr * goalness) list;;
val find_negtrans_right : string -> head -> (expr * goalness) list;;

val find_all_negtrans_left : head -> (expr * goalness) list;;
val find_all_negtrans_right : head -> (expr * goalness) list;;

(* ==== proof cache ==== *)

val add_proof : Mlproof.proof -> unit;;
val search_proof : unit -> Mlproof.proof option;;

(* ==== definitions ==== *)

val add_def : definition -> unit;;
val has_def : string -> bool;;
val get_def : string -> definition * expr list * expr;;

(* ==== depth of metavariables ==== *)

val add_meta : expr -> int -> unit;;
val remove_meta : expr -> unit;;
val get_meta : expr -> int;;

(* ==== numbering for formulas ==== *)

val get_number : expr -> int;;
val get_formula : int -> expr (* raises Not_found *);;

(* ==== numbering for tau-expressions ==== *)

val make_tau_name : expr -> string;;
