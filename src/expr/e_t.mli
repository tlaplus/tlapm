(* Syntax tree for expressions, and relevant functions.

Copyright (C) 2011  INRIA and Microsoft Corporation
*)
open Property
open Util


(** Type of bulleted lists.
[And] and [Or] are the standard TLA+
bulleted lists of 1 or more arguments.
[Refs] represents a generic conjunction
that can take 0, 1 or many arguments.

The 0-argument case is treated as
similar (but not identical) to TRUE,
the 1-argument case as the same as
no conjunction, and the many-argument
case as similar to [And].
*)
type bullet = And | Or | Refs
type quantifier = Forall | Exists
type modal_op = Box | Dia
type fairness_op  = Weak | Strong

(** Type representing arguments to
operators.

[Shape_op] represents an operator
argument of specified arity (>= 1).

[Shape_expr] represents an
expression argument.
*)
type shape =
  | Shape_expr
  | Shape_op of int

(** An "expression" is either
a TLA+ expression,
operator or sequent
*)
type expr = expr_ wrapped
and expr_ =
    (* operators *)
  | Ix of int
  | Opaque of string
  | Internal of Builtin.builtin
  | Lambda of (hint * shape) list * expr
    (* sequents *)
  | Sequent of sequent
    (* unified module and
    subexpression references *)
  | Bang of expr * sel list
    (* ordinary TLA+ expressions *)
  | Apply of expr * expr list
  | With of expr * Method.t
  | If of expr * expr * expr
  | List of bullet * expr list
  | Let of defn list * expr
  | Quant of quantifier * bounds * expr
  | Tquant of
        quantifier * hints * expr
  | Choose of
        hint * expr option * expr
  | SetSt of hint * expr * expr
  | SetOf of expr * bounds
  | SetEnum of expr list
  | Product of expr list
  | Tuple of expr list
  | Fcn of bounds * expr
  | FcnApp of expr * expr list
  | Arrow of expr * expr
  | Rect of (string * expr) list
  | Record of (string * expr) list
  | Except of expr * exspec list
  | Dot of expr * string
  | Sub of modal_op * expr * expr
  | Tsub of modal_op * expr * expr
  | Fair of fairness_op * expr * expr
  | Case of
        (expr * expr) list * expr option
  | String of string
  | Num of string * string
  | At of bool (*
      true -> @ from except or
      false -> @ from proof-step *)
  | Parens of expr * pform

and pform = pform_ wrapped
and pform_ =
  | Syntax
      (** actual parens in
      source syntax *)
  | Nlabel of string * hints
      (** named label *)
  | Xlabel of string * (hint * int) list
      (** indexed label *)

(** subexpression selectors *)
and sel =
  | Sel_down
  | Sel_num of int
  | Sel_left
  | Sel_right
  | Sel_at
  | Sel_inst of expr list
  | Sel_lab of string * expr list

(** Except specification *)
and exspec = expoint list * expr
and expoint =
  | Except_dot of string
  | Except_apply of expr

(** Bound variables *)
and bounds = bound list
and bound =
    hint * kind * bound_domain
and bound_domain =
  | No_domain
  | Domain of expr
  | Ditto

(** Definitions *)
and defn = defn_ wrapped
and defn_ =
  | Recursive of hint * shape
  | Operator of hint * expr
  | Instance of hint * instance
  | Bpragma of hint * expr * (
      (hint * backend_args) list list)

(** Instance *)
and instance = {
  (** arguments of the instance *)
  inst_args : hints ;
  (** the instanced module *)
  inst_mod  : string ;
  (** substitution *)
  inst_sub  : (hint * expr) list ;
}

(** The [sequent] type represents
(a generalisation of) TLA+
    ASSUME/PROVE forms
*)
and sequent = {
  (** antecedents *)
  context : hyp Deque.dq ;
  (** succeedent
  (always a TLA+ expression)
  *)
  active  : expr ;
}

and kind =
  | Constant | State | Action
  | Temporal | Unknown

and backend_args =
  | Bdef
  | Bstring of string
  | Bfloat of float

and backend_info =
  | Bwhich | Btimeout | Btactic

and backend_action =
  | All | Once

(** Antecedents of a sequent *)
and ctx = hyp Deque.dq
and hyp = hyp_ wrapped
and hyp_ =
  | Fresh of
        hint * shape * kind * hdom
  | Flex of hint
  | Defn of defn * wheredef *
            visibility * export
  | Fact of expr * visibility * time

and hdom = Unbounded
  | Bounded of expr * visibility

and wheredef = Builtin
  | Proof of time | User

and export = Local | Export

and visibility = Visible | Hidden

and time = Now | Always | NotSet

val unditto:
    bounds -> bounds
val name_of_bound:
    bound -> hint
val names_of_bounds:
    bounds -> hints
val string_of_bound:
    bound -> string
val strings_of_bounds:
    bounds -> string list
val bounds_of_variables:
    hints -> bounds
val bounds_of_parameters:
    (hint * shape) list -> bounds


module type Node_factory_sig =
sig
    type t

    (* construction of
    syntax-tree nodes *)
    val make_ix:
        int -> expr
    val make_opaque:
        t -> expr
    val make_internal:
        Builtin.builtin -> expr
    val make_arg:
        t -> (hint * shape)
    val make_lambda:
        t list -> expr -> expr
    val make_def:
        t -> expr -> defn
    val make_def_with_args:
        t -> t list ->
        expr -> defn
    val make_recursive_def:
        t -> shape -> defn
    val make_sequent:
        ctx -> expr -> expr
    val make_bang:
        expr -> sel list ->
        expr
    val make_apply:
        expr -> expr list ->
        expr
    val make_with:
        expr -> Method.t -> expr
    val make_if:
        expr -> expr ->
        expr -> expr
    val make_junction:
        bullet -> expr list ->
        expr
    val make_disjunction:
        expr list -> expr
    val make_conjunction:
        expr list -> expr
    val make_let:
        defn list -> expr -> expr
    val make_quantifier:
        quantifier -> bounds ->
        expr -> expr
    val make_exists:
        bounds -> expr -> expr
    val make_forall:
        bounds -> expr -> expr
    val make_temporal_exists:
        t list -> expr -> expr
    val make_temporal_forall:
        t list -> expr -> expr
    val make_choose:
        t -> expr -> expr
    val make_bounded_choose:
        t -> expr -> expr -> expr
    val make_setst:
        t -> expr -> expr -> expr
    val make_setof:
        expr -> bounds -> expr
    val make_setenum:
        expr list -> expr
    val make_product:
        expr list -> expr
    val make_tuple:
        expr list -> expr
    val make_fcn:
        bounds -> expr -> expr
    val make_fcn_domain:
        expr -> expr
    val make_fcn_app:
        expr -> expr -> expr
    val make_fcn_app_commas:
        expr -> expr list ->
        expr
    val make_fcn_set:
        expr -> expr -> expr
    val make_record_set:
        (t * expr) list -> expr
    val make_record:
        (t * expr) list -> expr
    val make_except:
        expr -> exspec list ->
        expr
    val make_dot:
        expr -> t -> expr
    val make_square_action:
        expr -> expr -> expr
    val make_angle_action:
        expr -> expr -> expr
    val make_subscripted_always:
        expr -> expr -> expr
    val make_subscripted_eventually:
        expr -> expr -> expr
    val make_weak_fairness:
        expr -> expr -> expr
    val make_strong_fairness:
        expr -> expr -> expr
    val make_case:
        (expr * expr) list ->
        expr option -> expr
    val make_string:
        t -> expr
    val make_number:
        t -> t -> expr
    val make_at: bool -> expr
    val make_parens:
        expr -> pform -> expr
    val make_const_decl:
        t -> bound
    val make_const_decls:
        t list -> bounds
    val make_bounded_const_decl:
        t -> expr -> bound
    val make_bounded_const_decls:
        (t * expr) list -> bounds
    val make_param_decl:
        t -> bound
    val make_param_decls:
        t list -> bounds
    val make_unbounded:
        t -> kind -> bound
    val make_bounded:
        t -> kind ->
        expr -> bound
    val make_fresh:
        t -> kind -> hyp
    val make_bounded_fresh:
        t -> expr -> hyp
    val make_fresh_with_arity:
        t -> kind -> int -> hyp
end


module From_string:
    Node_factory_sig with
    type t = string


module From_hint:
    Node_factory_sig with
    type t = hint


val get_val_from_id:
    'hyp Deque.dq -> int -> 'hyp
val name_of_ix:
    int -> ctx -> hint

(* fmt.ml *)
val hyp_name:
    hyp_ Property.wrapped -> string

val print_cx: ctx -> unit

val find_hyp_named:
    ctx -> string -> int * hyp
val cx_front: ctx -> int -> ctx
val scx_front:
    'a * ctx -> int -> 'a * ctx
val format_locus:
    'a wrapped -> string
val shape_to_arity: shape -> int

(* anon.ml *)
val exprify_sequent: sequent -> expr_

val sequent_stats: sequent -> int

val enabledaxioms: bool pfuncs
val has_enabledaxioms:
    'a Property.wrapped -> bool
val get_enabledaxioms:
    'a Property.wrapped -> bool
