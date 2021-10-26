(*
 * Copyright (C) 2011-2012  INRIA and Microsoft Corporation
 *)
open Expr.T

module SSet : Set.S with type elt = string
module SMap : Map.S with type key = string

module StringList : sig
  type t = string list
  val compare : t -> t -> int
end

module SSMap : Map.S with type key = StringList.t

module Int : sig
  type t = int
  val compare : t -> t -> int
end

module ISet : Set.S with type elt = Int.t

(****************************************************************************)
(* Combinators                                                              *)
(****************************************************************************)

val ( |> ) : 'a -> ('a -> 'b) -> 'b
val ( |>> ) : 'a * 'b -> ('a -> 'c) -> 'c * 'b
val ( ||> ) : 'a * 'b -> ('b -> 'c) -> 'a * 'c
val kk : unit -> 'a -> 'a
val tap : ('a -> unit) -> 'a -> 'a
val pairself : ('a -> 'b) -> ('a * 'a) -> ('b * 'b)

(****************************************************************************)

val verbosity : int ref

(* val ifprint : int -> ('a, unit, string, unit) format4 -> 'a *)
val ifprint : int -> ('a, Format.formatter, unit, unit) format4 -> 'a

val print_prop : unit -> Format.formatter -> Expr.T.expr -> unit

val pps_ex : (hyp list * expr) -> string

(* val printscx : hyp list -> unit *)

(****************************************************************************)

(* exception Unification_failed of string
exception Unsupported_type of string
exception Untyped_symbol of string
exception Infer_other of string
exception No_function_domain of string
exception Unsupported_expression of expr *)

val filter_true  : expr list -> expr list
val filter_false : expr list -> expr list

val smt_id : string -> string
val turn_first_char : bool -> string -> string
val lookup_id : hyp list -> int -> string
val is_bvar : hyp list -> int -> bool

val fcnapp : string

val applyint2u :   unit Property.pfuncs
val apply_int2u :  'a Property.wrapped -> bool
val applystr2u :   unit Property.pfuncs
val apply_str2u :  'a Property.wrapped -> bool
val applyu2bool :  unit Property.pfuncs
val apply_u2bool : 'a Property.wrapped -> bool
val boolify_prop :  unit Property.pfuncs
val has_boolify :  'a Property.wrapped -> bool
val fmtasint :     unit Property.pfuncs
val fmt_as_int :   'a Property.wrapped -> bool
val fmtasbool :    unit Property.pfuncs
val fmt_as_bool :  'a Property.wrapped -> bool
val pattern_prop : Expr.T.expr Property.pfuncs
val has_pattern : 'a Property.wrapped -> bool
val get_pattern : 'a Property.wrapped -> Expr.T.expr

(* val is_bounded_var : string -> bool *)
val is_nonbasic_var : string -> bool
val boundvar : unit Property.pfuncs
val has_boundvar : expr -> bool
(* val quant_id : string -> string *)

val unditto : bound list -> bound list
val add_bs_ctx : bound list -> hyp list -> hyp list

val n_to_list : int -> int list
(* val concat0 : string -> 'a list -> string *)
(* val concat1 : ('a -> string, unit, string) format -> 'a list -> string *)
(* val concat2 : ('a -> string, unit, string) format -> 'a list -> string *)
val remove_repeated : 'a list -> 'a list
val remove_repeated_ex : expr list -> expr list

val ctr : int ref
val unique_id : unit -> int
val fresh_name : unit -> string
val fresh_id : unit -> string

(* val prime : string -> string *)
(* val unprime_id : string -> string *)
val is_prime : string -> bool

val mk_string : string -> string

val split_domain :
  quantifier ->
  expr ->
  bound list ->
  bound list ->
  bound list * expr

val deconj : expr -> expr list
val deimpl : expr -> expr list * expr
val unroll_seq : sequent -> expr
val to_list : sequent -> ((unit * hyp Deque.dq) * expr list * expr)

val map_exp : (hyp list -> expr -> expr) -> hyp list -> expr -> expr
val map_list : (hyp list -> expr -> string list) -> hyp list -> expr -> string list
val opaque : ?strong:bool -> ?min:int -> hyp list -> expr -> expr

val free_n_vars : int -> hyp list -> expr -> bool

val fresh_bound_to_exp : string Property.wrapped -> expr -> expr * hyp

val map_default : ('a -> 'b) -> 'b -> 'a option -> 'b

(* val free_operators : hyp list -> expr -> string list *)
val free_operators : sequent -> string list
val fv : 'a Expr.Visit.scx -> sequent -> string list
val fv_expr : 'a Expr.Visit.scx -> expr -> string list

val fv_expr_i : int -> expr -> int list

val record_ids : int SSMap.t ref
val add_record_id : string list -> int
val get_recid : string list -> int

val tla_op_set : SSet.t ref
val add_tla_op : SSet.elt -> unit

val skolem2_ids : (expr * int * bool) SMap.t ref
val skolem1_ids : (hyp Deque.dq * expr * bool) SMap.t ref
val record_signatures : ((string list) list) ref
val nonbasic_prefix : string

val chooses : (hyp list * expr) SMap.t ref
val add_choose : string -> hyp list -> expr -> unit

type provermode = Smtlib | CVC3 | Z3 | Yices | Spass | Fof
val mode : provermode ref

val typesystem_mode : int ref

class simplefact : object
  val mutable sf : (hyp Deque.dq * expr) list
  method reset : unit
  method print : unit
  (* method add : hyp Deque.dq -> expr list -> unit *)
  method push : hyp Deque.dq -> expr list -> int
  method private mem : hyp Deque.dq -> expr -> bool
  method simpl : hyp Deque.dq -> expr -> expr
  (* method remove :  expr list -> unit *)
  method pop :  int -> unit
end

val sf : simplefact

val simplefacts : (hyp list * Expr.T.expr) list ref
val add_simplefact : hyp list -> expr -> unit
val remove_simplefact : expr list -> unit
val simp_simplefacts : hyp list -> expr -> expr

val perms : 'a list -> ('a * 'a) list

val is_term : expr -> bool
val is_domain : expr -> bool

(* val unprime : hyp list -> expr -> expr *)
val renameb : hyp list -> expr -> expr

val newvars : (hyp list * expr) SMap.t ref
val mk_newvar_id : hyp list -> expr -> string
val unspec : hyp list -> expr -> expr
val insert_intdiv_cond : hyp list -> expr -> expr

val subtract : 'a list -> 'a -> 'a list
val list_minus : 'a list -> 'a list -> 'a list

val flatten_conj : expr -> expr
val flatten_disj : expr -> expr

val fix : ?feq:(expr -> expr -> bool) -> int -> (expr list -> expr list) -> expr list -> expr list
val fix3 : int ->
    (((unit * hyp Deque.dq) * hyp Deque.dq * expr) -> ((unit * hyp Deque.dq) * hyp Deque.dq * expr)) ->
    ((unit * hyp Deque.dq) * hyp Deque.dq * expr) ->
    ((unit * hyp Deque.dq) * hyp Deque.dq * expr)
val fix_sq : int -> (sequent -> sequent) -> sequent -> sequent
val fix_sqs : int -> (sequent list -> sequent list) -> sequent list -> sequent list

val to_cx : hyp Deque.dq -> hyp list
val to_scx : hyp list -> hyp Deque.dq

val is_typhyp : ?var:string -> hyp Deque.dq -> expr -> bool

val unb : bounds -> bounds * (expr list)

val rec_sort : (string * 'a) list -> (string * 'a) list

(* val deque_to_ctx : Isabelle.ctx -> hyp Deque.dq -> Isabelle.ctx *)

val is_smt_kwd : string -> bool
val smt_pickle : bool -> string -> string
