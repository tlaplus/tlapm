(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

module T : sig
  open Property;;
  open Util;;

  (** Type of bulleted lists. [And] and [Or] are the standard TLA+
      bulleted lists of 1 or more arguments. [Refs] represents a
      generic conjunction that can take 0, 1 or many arguments. The
      0-argument case is treated as similaar (but not identical) to
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

  val get_val_from_id : 'hyp Deque.dq -> int -> 'hyp;;
  val hyp_name : hyp -> string;;
  val exprify_sequent : sequent -> expr_;;
end;;

module Fmt : sig
  open T
  open Ctx
  type ctx = hyp Deque.dq * int Ctx.ctx
  val bump : ctx -> ctx
  val adj : ctx -> Util.hint -> ctx * string
  val adjs : ctx -> Util.hint list -> ctx * string list
  val fmt_bounds :
    ctx -> bound list -> ctx * (Format.formatter -> unit)
  val extend_bounds :
    ?prevdom:expr option ->
    ctx -> bound list -> ctx * (string * expr option) list
  val pp_print_shape : Format.formatter -> shape -> unit
  val pp_print_bound :
    ctx -> Format.formatter -> string * expr option -> unit
  val fmt_expr : ?temp:bool -> ctx -> expr -> Tla_parser.Fu.exp
  val pp_print_expr : ?temp:bool -> ctx -> Format.formatter -> expr -> unit
  val pp_print_defn : ctx -> Format.formatter -> defn -> ctx
  val pp_print_defns : ctx -> Format.formatter -> defn list -> ctx
  val pp_print_sequent : ?temp:bool -> ctx -> Format.formatter -> sequent -> ctx
  val pp_print_hyp : ?temp:bool -> ctx -> Format.formatter -> hyp -> ctx
  val pp_print_instance : ctx -> Format.formatter -> instance -> unit
  val string_of_expr : hyp Deque.dq  -> expr -> string
end;;

module Subst : sig
  open Property
  open T
  type sub
  val shift : int -> sub
  val scons : expr -> sub -> sub
  val bumpn : int -> sub -> sub
  val bump : sub -> sub
  val compose : sub -> sub -> sub
  val app_ix : sub -> int wrapped -> expr
  val normalize : ?cx:hyp Deque.dq -> expr -> expr list -> expr_
  val app_expr : sub -> expr -> expr
  val app_bdom : sub -> bound_domain -> bound_domain
  val app_bound : sub -> bound -> sub * bound
  val app_bounds : sub -> bound list -> sub * bound list
  val app_defn : sub -> defn -> defn
  val app_defns : sub -> defn list -> sub * defn list
  val app_sequent : sub -> sequent -> sequent
  val app_hyp : sub -> hyp -> hyp
end;;

module Visit : sig
  open T
  type 's scx = 's * hyp Deque.dq
  val adj  : 's scx -> hyp -> 's scx
  val adjs : 's scx -> hyp list -> 's scx
  class virtual ['s] map : object
    method expr     : 's scx -> expr -> expr
    method pform    : 's scx -> pform -> pform
    method sel      : 's scx -> sel -> sel
    method sequent  : 's scx -> sequent -> 's scx * sequent
    method defn     : 's scx -> defn -> defn
    method defns    : 's scx -> defn list -> 's scx * defn list
    method bounds   : 's scx -> bound list -> 's scx * bound list
    method bound    : 's scx -> bound -> 's scx * bound
    method exspec   : 's scx -> exspec -> exspec
    method instance : 's scx -> instance -> instance
    method hyp      : 's scx -> hyp -> 's scx * hyp
    method hyps     : 's scx -> hyp Deque.dq -> 's scx * hyp Deque.dq
  end
  class virtual ['s] iter : object
    method expr     : 's scx -> expr -> unit
    method pform    : 's scx -> pform -> unit
    method sel      : 's scx -> sel -> unit
    method sequent  : 's scx -> sequent -> 's scx
    method defn     : 's scx -> defn -> 's scx
    method defns    : 's scx -> defn list -> 's scx
    method bounds   : 's scx -> bounds (*list*) -> 's scx
    method bound    : 's scx -> bound -> 's scx
    method exspec   : 's scx -> exspec -> unit
    method instance : 's scx -> instance -> unit
    method hyp      : 's scx -> hyp -> 's scx
    method hyps     : 's scx -> hyp Deque.dq -> 's scx
  end
end;;

module Eq : sig
  open T
  val expr : expr -> expr -> bool
  val hyp : hyp -> hyp -> bool
  val sequent : sequent -> sequent -> bool
end;;

module Deref : sig
  val badexp : T.expr;;
end;;

module Leibniz : sig
  open T
  val is_leibniz : 'a Property.wrapped -> int -> bool
  class virtual leibniz_visitor : object
  inherit [unit] Visit.map
    method expr     : unit Visit.scx -> expr -> expr
    method pform    : unit Visit.scx -> pform -> pform
    method sel      : unit Visit.scx -> sel -> sel
    method sequent  : unit Visit.scx -> sequent -> unit Visit.scx * sequent
    method defn     : unit Visit.scx -> defn -> defn
    method defns    : unit Visit.scx -> defn list -> unit Visit.scx * defn list
    method bounds   : unit Visit.scx -> bound list -> unit Visit.scx * bound list
    method bound    : unit Visit.scx -> bound -> unit Visit.scx * bound
    method exspec   : unit Visit.scx -> exspec -> exspec
    method instance : unit Visit.scx -> instance -> instance
    method hyp      : unit Visit.scx -> hyp -> unit Visit.scx * hyp
    method hyps     : unit Visit.scx -> hyp Deque.dq -> unit Visit.scx * hyp Deque.dq
  end
end;;

module Constness : sig
  open T
  val is_const : 'a Property.wrapped -> bool
  class virtual const_visitor : object
  inherit [unit] Visit.map
    method expr     : unit Visit.scx -> expr -> expr
    method pform    : unit Visit.scx -> pform -> pform
    method sel      : unit Visit.scx -> sel -> sel
    method sequent  : unit Visit.scx -> sequent -> unit Visit.scx * sequent
    method defn     : unit Visit.scx -> defn -> defn
    method defns    : unit Visit.scx -> defn list -> unit Visit.scx * defn list
    method bounds   : unit Visit.scx -> bound list -> unit Visit.scx * bound list
    method bound    : unit Visit.scx -> bound -> unit Visit.scx * bound
    method exspec   : unit Visit.scx -> exspec -> exspec
    method instance : unit Visit.scx -> instance -> instance
    method hyp      : unit Visit.scx -> hyp -> unit Visit.scx * hyp
    method hyps     : unit Visit.scx -> hyp Deque.dq -> unit Visit.scx * hyp Deque.dq
  end
end;;

module Tla_norm : sig
  val expand_unchanged : unit Visit.scx -> T.expr -> T.expr
  val expand_action : unit Visit.scx -> T.expr -> T.expr
  val expand_leadsto : unit Visit.scx -> T.expr -> T.expr
  val expand_fairness : unit Visit.scx -> T.expr -> T.expr
end;;


module Temporal_props : sig
  val compute_time : T.hyp Deque.dq -> T.expr -> T.time
  val check_time_change : T.hyp Deque.dq -> T.time -> T.time
end;;

module Elab : sig
  open T
  (* moved to action frontend *)
  (* val prime_normalize : hyp Deque.dq -> expr -> expr *)
  val normalize : hyp Deque.dq -> expr -> expr
  val replace_at : unit Visit.scx -> expr -> expr -> expr
  val get_at : expr -> expr
end;;

module Anon : sig
  open T
  val hyp_is_named : string -> hyp -> bool
  class anon : [string list] Visit.map
  val anon : anon
end;;

module Parser : sig
  open Tla_parser
  open T
  val expr : bool -> T.expr lprs
  val bounds : bool -> T.bound list lprs
  val defn : bool -> T.defn lprs
  val instance : bool -> T.instance lprs
  val sequent : bool -> T.sequent lprs
  val opdecl : (Util.hint * shape) lprs
end;;
