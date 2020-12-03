(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

open Property;;
open Util;;

(** Type of bulleted lists. [And] and [Or] are the standard TLA+
    bulleted lists of 1 or more arguments. [Refs] represents a
    generic conjunction that can take 0, 1 or many arguments. The
    0-argument case is treated as similar (but not identical) to
    TRUE, the 1-argument case as the same as no conjunction, and the
    many argument case as similar to [And]. *)
type bullet  = And | Or | Refs

type quantifier = Forall | Exists

type modal_op = Box | Dia

type fairness_op  = Weak | Strong

(** Type representing arguments to operators, sometimes conflated with
    "arity" in the TLA+ book. [Shape_op] represents an operator
    argument of specified arity (>= 1). [Shape_expr] represents an
    expression argument. *)
type shape =
  | Shape_expr
  | Shape_op of int

(** An "expression" is either a TLA+ expression, operator or sequent *)
type expr = expr_ wrapped
and expr_ =
    (* operators *)
  | Ix of int
  | Opaque of string
  | Internal of Builtin.builtin
  | Lambda of (hint * shape) list * expr
    (* sequents *)
  | Sequent of sequent
    (* unified module and subexpression references *)
  | Bang of expr * sel list
    (* ordinary TLA+ expressions *)
  | Apply of expr * expr list
  | With of expr * Method.t
  | If of expr * expr * expr
  | List of bullet * expr list
  | Let of defn list * expr
  | Quant of quantifier * bounds * expr
  | Tquant of quantifier * hint list * expr
  | Choose of hint * expr option * expr
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
  | Case of (expr * expr) list * expr option
  | String of string
  | Num of string * string
  | At of bool (* true -> @ from except / false -> @ from proof-step *)
  | Parens of expr * pform

and pform = pform_ wrapped
and pform_ =
  | Syntax
      (** actual parens in source syntax *)
  | Nlabel of string * hint list
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
and bound = hint * kind * bound_domain
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
  | Bpragma of hint * expr * ((hint * backend_args) list list)

(** Instance *)
and instance = {
  (** arguments of the instance *)
  inst_args : hint list ;

  (** the instanced module *)
  inst_mod  : string ;

  (** substitution *)
  inst_sub  : (hint * expr) list ;
}

(** The [sequent] type represents (a generalisation of) TLA+
    ASSUME/PROVE forms *)
and sequent = {
  (** antecedents *)
  context : hyp Deque.dq ;

  (** succeedent (always a TLA+ expression) *)
  active  : expr ;
}

and kind =
  | Constant | State | Action | Temporal | Unknown

and backend_args =
  | Bdef
  | Bstring of string
  | Bfloat of float

and backend_info =
  | Bwhich | Btimeout | Btactic

and backend_action =
  | All | Once

(** Antecedents of a sequent *)
and hyp = hyp_ wrapped
and hyp_ =
  | Fresh of hint * shape * kind * hdom
  | Flex of hint
  | Defn of defn * wheredef * visibility * export
  | Fact of expr * visibility * time

and hdom = Unbounded | Bounded of expr * visibility

and wheredef = Builtin | Proof of time | User

and export = Local | Export

and visibility = Visible | Hidden

and time = Now | Always | NotSet
;;

(* SMT-LIB pattern attached to the body of a quantified expr *)
type pat = expr list;;
val pattern_prop : pat list pfuncs;;

val add_pats : expr -> pat list -> expr;;
val remove_pats : expr -> expr;;
val map_pats : (pat -> pat) -> expr -> expr;;

val get_val_from_id : 'hyp Deque.dq -> int -> 'hyp;;

(* fmt.ml *)
val hyp_hint : hyp_ Property.wrapped -> hint;;
val hyp_name : hyp_ Property.wrapped -> string;;

(* anon.ml *)
val exprify_sequent : sequent -> expr_;;
