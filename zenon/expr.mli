(*  Copyright 2003 INRIA  *)

type private_info;;


type expr = private
  | Evar of string * private_info
  | Emeta of expr * private_info    (* expr = Eall (...)  or   Eex (...) *)
  | Eapp of string * expr list * private_info

  | Enot of expr * private_info
  | Eand of expr * expr * private_info
  | Eor of expr * expr * private_info
  | Eimply of expr * expr * private_info
  | Eequiv of expr * expr * private_info
  | Etrue
  | Efalse

  | Eall of expr * string * expr * private_info
  | Eex of expr * string * expr * private_info
  | Etau of expr * string * expr * private_info
  | Elam of expr * string * expr * private_info
      (* variable, type, body *)
;;

type definition =
  | DefReal of string * string * expr list * expr * string option
     (* definition-name, defined-ident, params, body, decreasing-arg *)
  | DefPseudo of (expr * int) * string * expr list * expr
  | DefRec of expr * string * expr list * expr
;;

type t = expr;;

val equal : t -> t -> bool;;
val compare : t -> t -> int;;
val hash : t -> int;;

val evar : string -> expr;;
val emeta : expr -> expr;;
val eapp : string * expr list -> expr;;

val enot : expr -> expr;;
val eand : expr * expr -> expr;;
val eor : expr * expr -> expr;;
val eimply : expr * expr -> expr;;
val eequiv : expr * expr -> expr;;
val etrue : expr;;
val efalse : expr;;
val eall : expr * string * expr -> expr;;
val eex : expr * string * expr -> expr;;
val etau : expr * string * expr -> expr;;
val elam : expr * string * expr -> expr;;

val all_list : expr list -> expr -> expr;;
val ex_list : expr list -> expr -> expr;;

val diff : expr list -> expr list -> expr list;;
(* [diff l1 l2]
   return [l1] without the formulas present in [l2]
*)
val union : expr list -> expr list -> expr list;;
(* [union l1 l2]
   return [l1 @@ l2], removing duplicate formulas
*)
val disjoint : expr list -> expr list -> bool;;
(* [disjoint l1 l2]
   return true if [l1] and [l2] have no element in common
*)

val preunifiable : expr -> expr -> bool;;
(* [preunifiable e1 e2]
   Returns true if e1 and e2 are pre-unifiable.
   Assumes that e1 and e2 are terms (i.e. don't have logical connectives
   except inside a tau).
*)

val preunify : expr -> expr -> (expr * expr) list;;
(* [preunify e1 e2]
   If e1 and e2 are pre-unifiable, return the set of pre-unifiers.
   Return an empty list if they are not pre-unifiable.
   A pre-unifier is: (metavariable, value)
*)

val occurs_as_meta : expr -> expr -> bool;;
(* [occurs e1 e2] returns true if [Emeta (e1, _)] occurs in [e2] *)

exception Higher_order;;
val substitute : (expr * expr) list -> expr -> expr;;
val substitute_2nd : (expr * expr) list -> expr -> expr;;
val apply : expr -> expr -> expr;;
val add_argument : expr -> expr -> expr;;
val remove_scope : expr -> expr;;

(* gensym *)
val newvar : unit -> expr;;
val newname : unit -> string;;

val size : expr -> int;;
val get_taus : expr -> int;;   (* tau nesting level *)
val has_metas : expr -> bool;;
val count_metas : expr -> int;;
val get_metas : expr -> expr list;;
val get_fv : expr -> string list;;

type goalness = int;;

val print_stats : out_channel -> unit;;
