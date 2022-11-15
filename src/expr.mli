(* Package of modules for working with TLA+ expressions.

Copyright (C) 2011-2019  INRIA and Microsoft Corporation
*)
module T: sig
  open Property
  open Util

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

  (** Type representing arguments to operators.
      [Shape_op] represents an operator
      argument of specified arity (>= 1).
      [Shape_expr] represents an
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
    | Tquant of quantifier * hints * expr
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
    | Bpragma of hint * expr * ((hint * backend_args) list list)

  (** Instance *)
  and instance = {
    (** arguments of the instance *)
    inst_args : hints ;

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
  and ctx = hyp Deque.dq
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

  val unditto: bounds -> bounds

  val name_of_bound: bound -> hint
  val names_of_bounds: bounds -> hints
  val string_of_bound: bound -> string
  val strings_of_bounds:
      bounds -> string list
  val bounds_of_variables:
      hints -> bounds
  val bounds_of_parameters:
      (hint * shape) list -> bounds

  (** Fact name and kind *)
  type meta = {
    hkind : hyp_kind ;
    name : string ;
  }
  and hyp_kind = Axiom | Hypothesis | Goal
  val meta_prop : meta pfuncs


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


  val get_val_from_id: 'hyp Deque.dq -> int -> 'hyp
  val name_of_ix:
      int -> ctx -> hint
  val hyp_hint : hyp -> hint
  val hyp_name: hyp -> string

  val print_cx: ctx -> unit
  val find_hyp_named : ctx -> string -> int * hyp
  val cx_front : ctx -> int -> ctx
  val scx_front : 'a * ctx -> int -> 'a * ctx
  val format_locus : 'a wrapped -> string
  val shape_to_arity : shape -> int

  val exprify_sequent : sequent -> expr_

  val sequent_stats : sequent -> int

  val enabledaxioms : bool pfuncs
  val has_enabledaxioms : 'a Property.wrapped -> bool
  val get_enabledaxioms : 'a Property.wrapped -> bool
end


module Fmt: sig
    open T
    open Ctx
    type ctx = hyp Deque.dq * int Ctx.ctx
    val bump:
        ctx -> ctx
    val adj:
        ctx -> Util.hint ->
            ctx * string
    val adjs:
        ctx -> Util.hints ->
            ctx * string list
    val is_letter:
        char -> bool
    val is_hidden:
        hyp -> bool
    val elide:
        hyp -> bool
    val fmt_bounds:
        ctx -> bound list ->
            ctx * (Format.formatter -> unit)
    val extend_bounds:
        ?prevdom:expr option ->
        ctx -> bound list ->
            ctx * (string * expr option) list
    val pp_print_shape:
        Format.formatter -> shape ->
            unit
    val pp_print_var:
        Format.formatter -> Util.hint ->
            unit
    val pp_print_bound:
        ctx -> Format.formatter ->
        string * expr option ->
            unit
    val fmt_expr:
        ?temp:bool ->
        ctx -> expr ->
            Tla_parser.Fu.exp
    val pp_print_expr:
        ?temp:bool -> ctx ->
        Format.formatter -> expr ->
            unit
    val pp_print_defn:
        ctx -> Format.formatter ->
        defn ->
            ctx
    val pp_print_defns:
        ctx -> Format.formatter ->
        defn list ->
            ctx
    val pp_print_sequent:
        ?temp:bool -> ctx ->
        Format.formatter -> sequent ->
            ctx
    val pp_print_hyp:
        ?temp:bool -> ctx ->
        Format.formatter -> hyp ->
            ctx
    val pp_print_instance:
        ctx -> Format.formatter ->
        instance ->
            unit
    val string_of_expr:
        hyp Deque.dq -> expr ->
            string
end


module Subst: sig
    open Property
    open T
    type sub
    val shift:
        int -> sub
    val scons:
        expr -> sub ->
            sub
    val bumpn:
        int -> sub ->
            sub
    val bump:
        sub -> sub
    val compose:
        sub -> sub ->
            sub
    val app_ix:
        sub -> int wrapped ->
            expr
    val normalize:
        ?cx:hyp Deque.dq ->
        expr -> expr list ->
            expr_
    val app_expr:
        sub -> expr ->
            expr
    val app_bdom:
        sub -> bound_domain ->
            bound_domain
    val app_bound:
        sub -> bound ->
            sub * bound
    val app_bounds:
        sub -> bound list ->
            sub * bound list
    val app_defn:
        sub -> defn ->
            defn
    val app_defns:
        sub -> defn list ->
            sub * defn list
    val app_sequent:
        sub -> sequent ->
            sequent
    val app_hyp:
        sub -> hyp ->
            hyp

    class map: object
        method expr:
            sub -> expr ->
                expr
        method exprs:
            sub -> expr list ->
                expr list
        method pform:
            sub -> pform ->
                pform
        method sels:
            sub -> sel list ->
                sel list
        method sel:
            sub -> sel -> sel
        method sequent:
            sub -> sequent ->
                sub * sequent
        method defn:
            sub -> defn ->
                sub * defn
        method defns:
            sub -> defn list ->
                sub * defn list
        method bounds:
            sub -> bound list ->
                sub * bound list
        (* TODO: method bound:
            sub -> bound ->
                sub * bound *)
        method bound:
            sub -> bound ->
                bound
        method exspec:
            sub -> exspec ->
                exspec
        method instance:
            sub -> instance ->
                instance
        method hyp:
            sub -> hyp ->
                sub * hyp
        method hyps:
            sub -> hyp Deque.dq ->
                sub * hyp Deque.dq
        method normalize:
            ?cx:hyp Deque.dq ->
            expr -> expr list ->
                expr_
    end

    class map_visible_hyp: map
end


module Visit: sig
  open T
  val hyp_of_bound_full: bound -> hyp
  val hyps_of_bounds: bounds -> hyp list
  val hyps_of_bounds_full: bounds -> hyp list
  val hyps_of_bounds_unditto: bounds -> hyp list
  val hyps_of_bounds_as_arity_0: bounds -> hyp list
  val map_bound_domains:
      (expr -> expr) -> bounds -> bounds
  val map_bounds:
      (Util.hint -> Util.hint) -> (expr -> expr) -> bounds -> bounds
  val rename_bound: bound -> Util.hint -> bound
  val rename_bounds: bounds -> Util.hints -> bounds
  type 's scx = 's * hyp Deque.dq
  val adj  : 's scx -> hyp -> 's scx
  val adjs : 's scx -> hyp list -> 's scx
  val adj_unboundeds_unchecked: 's scx -> bounds -> 's scx
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
    method adj      : 's scx -> hyp -> 's scx
    method adjs     : 's scx -> hyp list -> 's scx
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
  class virtual ['s] map_visible_hyp : ['s] map
  class virtual ['s] iter_visible_hyp : ['s] iter

  class virtual ['s] map_rename : object
      inherit ['s] map
      method rename : ctx -> hyp -> Util.hint -> hyp * Util.hint
      method renames : ctx -> hyp list -> Util.hints -> hyp list * Util.hints
  end
end

module Eq: sig
    open T
    val expr:
        expr -> expr -> bool
    val hyp:
        hyp -> hyp -> bool
    val sequent:
        sequent -> sequent -> bool
end


module Deref: sig
    val badexp: T.expr
end


module Leibniz: sig
    open T
    val is_leibniz:
        'a Property.wrapped -> int ->
            bool

    class virtual leibniz_visitor:
        [unit] Visit.map
end


module Constness: sig
    open T
    val is_const:
        'a Property.wrapped -> bool
    val has_const:
        'a Property.wrapped -> bool
    class virtual const_visitor:
        [unit] Visit.map
end


module Tla_norm: sig
    val rewrite_unch:
        T.expr -> T.expr
    val expand_unchanged:
        unit Visit.scx -> T.expr -> T.expr
    val expand_action:
        unit Visit.scx -> T.expr -> T.expr
    val expand_leadsto:
        unit Visit.scx -> T.expr -> T.expr
    val expand_fairness:
        unit Visit.scx -> T.expr -> T.expr
end


module Temporal_props: sig
    val compute_time:
        T.hyp Deque.dq -> T.expr -> T.time
    val check_time_change:
        T.hyp Deque.dq -> T.time -> T.time
end


module Elab: sig
    open T
    (* moved to action frontend *)
    (* val prime_normalize : hyp Deque.dq -> expr -> expr *)
    val normalize:
        hyp Deque.dq -> expr -> expr
    val replace_at:
        unit Visit.scx -> expr -> expr -> expr
    val get_at:
        expr -> expr
end


module Anon: sig
    open T
    val hyp_is_named: string -> hyp -> bool
    class anon: [string list] Visit.map
    val anon: anon
end


module Parser: sig
    open Tla_parser
    open T
    val expr: bool -> T.expr lprs
    val bounds: bool -> T.bound list lprs
    val defn: bool -> T.defn lprs
    val instance: bool -> T.instance lprs
    val sequent: bool -> T.sequent lprs
    val opdecl: (Util.hint * shape) lprs
end


module Levels: sig
    open Property
    open T
    open Visit
    module StringSet:
        Set.S
        with type elt = string

    type level_info = LevelInfo of
        int * bool list * StringSet.t

    val exprlevel:
        level_info pfuncs
    val has_level:
        'a Property.wrapped -> bool
    val rm_level:
        'a Property.wrapped -> 'a Property.wrapped
    val get_level_info:
        'a Property.wrapped -> level_info
    val get_level:
        'a Property.wrapped -> int
    val get_level_weights:
        'a Property.wrapped -> bool list
    val get_level_args:
        'a Property.wrapped -> StringSet.t
    val assert_has_correct_level:
        expr -> unit
    val kind_to_level:
        kind -> int

    class virtual ['s] level_computation:
        ['s] Visit.map
    class virtual ['s] _rm_expr_level:
        ['s] Visit.map

    val compute_level:
        ctx -> expr -> expr
    val rm_expr_level:
        ctx -> expr -> expr
end


module Action: sig
    open T
    val invert_renaming:
        ctx -> expr ->
            expr
    val implication_to_enabled:
        ctx -> expr ->
            expr
    val lambdify:
        ctx -> expr ->
        lambdify_enabled:bool ->
        lambdify_cdot:bool ->
        autouse:bool ->
            expr
    val quantify:
        ctx -> expr ->
        expand_enabled:bool ->
        expand_cdot:bool ->
            expr
    val expand_action_operators:
        ctx -> expr ->
        expand_enabled:bool ->
        expand_cdot:bool ->
        autouse:bool ->
            expr
end


module SubstOp: sig
    open Property
    open T
    type substitutive_args = bool array

    val substitutive_arg:
        substitutive_args pfuncs
    val has_substitutive:
        'a Property.wrapped -> bool
    val get_substitutive:
        'a Property.wrapped -> substitutive_args
    val get_substitutive_arg:
        'a Property.wrapped -> int -> bool

    val compute_subst:
        ctx -> expr -> expr
end


module LevelComparison: sig
    open Property
    open Util
    open T
    class level_comparison : object
        method compare:
            ctx -> ctx ->
            expr -> expr ->
                bool
        method expr:
            ctx -> ctx ->
            expr -> expr ->
                bool
        method exprs:
            ctx -> ctx ->
            expr list -> expr list ->
                bool
        method bounds_cx:
            ctx -> bounds ->
                ctx
        method bounds:
            ctx -> ctx ->
            bounds -> bounds ->
                bool
        method bound:
            ctx -> ctx ->
            bound -> bound ->
                bool
        method bdom:
            ctx -> ctx ->
            bound_domain -> bound_domain ->
                bool
        method opt_expr:
            ctx -> ctx ->
            expr option -> expr option ->
                bool
        method defns_cx:
            ctx -> defn list -> ctx
        method defns:
            ctx -> ctx ->
            defn list -> defn list ->
                bool
        method defn:
            ctx -> ctx ->
            defn -> defn ->
                bool
        method sequent:
            ctx -> ctx ->
            sequent -> sequent ->
                bool
        method context:
            ctx -> ctx ->
            ctx -> ctx ->
                bool
        method hyps_cx:
            ctx -> ctx ->
                ctx
        method hyp:
            ctx -> ctx ->
            hyp -> hyp ->
                bool
        method hyp_cx:
            ctx -> hyp ->
                ctx
        method instance:
            ctx -> ctx ->
            instance -> instance ->
                bool
        method sub:
            ctx -> ctx ->
            (hint * expr) list ->
            (hint * expr) list ->
                bool
        method sel:
            ctx -> ctx ->
            sel -> sel ->
                bool
    end

    val check_level_change:
        ctx -> expr -> expr
end
