(* Syntax tree for expressions, and relevant functions.

Copyright (C) 2008-2019  INRIA and Microsoft Corporation
*)
open Ext
open Property
open Util


(** Type of bulleted lists.
[And] and [Or] are the standard TLA+
bulleted lists of 1 or more arguments.
[Refs] represents a generic conjunction
that can take 0, 1 or many arguments.

The 0-argument case is treated as similaar
(but not identical) to TRUE,
the 1-argument case as the same as
no conjunction, and the many-argument case
as similar to [And].
*)
type bullet  = And | Or | Refs

type quantifier = Forall | Exists

type modal_op = Box | Dia

type fairness_op  = Weak | Strong

(* Type representing arguments to operators.
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
an operator, or
a sequent *)
type expr = expr_ wrapped
and expr_ =
    (* operators *)
    (* de Bruijn index *)
  | Ix of int
    (* identifier name *)
  | Opaque of string
    (* builtin operator *)
  | Internal of Builtin.builtin
    (* `LAMBDA` and
    signatures of operator definitions *)
  | Lambda of (hint * shape) list * expr
    (* sequents (`ASSUME`/`PROVE` with
    definitions from module scope) *)
  | Sequent of sequent
    (* unified module and
    subexpression references (Foo!Op) *)
  | Bang of expr * sel list
    (* ordinary TLA+ expressions *)
    (* operator application `Op(arg1, arg2)` *)
  | Apply of expr * expr list
    (* Expression annotated with
    prover directive. *)
  | With of expr * Method.t
    (* Ternary conditional `IF P THEN A ELSE B` *)
  | If of expr * expr * expr
    (* Conjunction and disjunction lists *)
  | List of bullet * expr list
    (* `LET` *)
  | Let of defn list * expr
    (* rigid quantification `\E` or `\A` *)
  | Quant of quantifier * bounds * expr
    (* temporal quantification `\EE` or `\AA` *)
  | Tquant of quantifier * hints * expr
    (* Two cases (unbounded and bounded `CHOOSE`):

    - `CHOOSE x:  pred`, for example:
       ```ocaml
       let x = noprops "x" in
       Choose (x, None, pred)
       ```

    - `CHOOSE x \in S:  pred`, for example:
      ```ocaml
      let x = noprops "x" in
      Choose (x, Some S, pred)
      ```
    *)
  | Choose of hint * expr option * expr
    (* `{x \in S:  P(x)}`
    axiom scheme of separation

    Section 16.1.6 on pages 299--301 of
    the book "Specifying Systems",
    specifically page 301.

    Elements:
    1. declared identifier (`x` above),
    2. set (`S` above) that bounds the
       values of the identifier
    3. predicate (`P(x)` above)
    *)
  | SetSt of hint * expr * expr
    (* `{f(x):  x \in S}`
    axiom scheme of replacement

    Section 16.1.6 on pages 299--301 of
    the book "Specifying Systems",
    specifically page 301.
    *)
  | SetOf of expr * bounds
    (* `{1, 2}`
    set enumeration

    Section 16.1.6 on pages 299--301 of
    the book "Specifying Systems",
    specifically page 300.
    *)
  | SetEnum of expr list
    (* Cartesian product *)
  | Product of expr list
    (* `<<1, 2>>` *)
  | Tuple of expr list
    (* Function constructor `[x \in S |-> e]` *)
  | Fcn of bounds * expr
    (* `f[x]` *)
  | FcnApp of expr * expr list
    (* Set of functions `[A -> B]` *)
  | Arrow of expr * expr
  (* [h: S, ...] *)
  | Rect of (string * expr) list
  (* [h |-> v, ...] *)
  | Record of (string * expr) list
  | Except of expr * exspec list
  | Dot of expr * string
    (* Subscripted (action) expressions:
    `[A]_v` and `<< A >>_v` *)
  | Sub of modal_op * expr * expr
    (* Temporal subscripted expressions:
    `[][A]_v` and `<><< A >>_v` *)
  | Tsub of modal_op * expr * expr
    (* `WF_` and `SF_` *)
  | Fair of fairness_op * expr * expr
    (* `CASE` *)
  | Case of (expr * expr) list * expr option
  | String of string
  | Num of string * string
  | At of bool  (* where:
      `true` means `@` from `EXCEPT`, and
      `false` means `@` from a proof step. *)
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
and bound = hint * kind * bound_domain
and bound_domain =
  | No_domain
  | Domain of expr
  | Ditto

(** Definitions

- Used in LET scope.
- Used within Defn when in antecedents.
*)
and defn = defn_ wrapped
and defn_ =
    (* recursive operator definition
    Results by expanding in the
    function `hyps_of_modunit`
    a `RECURSIVE` section represented
    by `Module.T.Recursives`.
    *)
  | Recursive of hint * shape
    (*
    operator definition:
    - name `hint`
    - body `expr`:
      - if arity is <_, ... >,
        then a `Lambda (args, expr)`, with:
        - `args`: the signature of
          the operator definition
        - `expr`: the expression of
          the body of the operator definition.
      - if arity is _, then the expression
        of the definition body.
    *)
  | Operator of hint * expr
    (* parameter substitution for instantiation *)
  | Instance of hint * instance
  | Bpragma of
        hint * expr * (
            (hint * backend_args) list list)

(* Instance *)
and instance = {
  (** arguments of the statement `INSTANCE`,
  for example:

    let wrap (x: string): hint = noprops x in
    List.map wrap ["x"; "y"]
  *)
  inst_args : hints ;

  (* name of the instantiated module *)
  inst_mod  : string ;

  (** substitution defined by the
  statement `INSTANCE`, for example:

    let wrap (x: string): hint = noprops x in
    let expr1 = noprops (Opaque "p")
    let expr2 =
        let op = noprops (Internal Builtin.Plus) in
        let arg1 = noprops (Opaque "q") in
        let arg2 = noprops (Opaque "r") in
        noprops (op [arg1; arg2])
    in

    [ (wrap("x"), expr1);
      (wrap("y"), expr2) ]
  *)
  inst_sub  : (hint * expr) list ;
}

(** The [sequent] type represents
(a generalisation of) TLA+
ASSUME/PROVE forms *)
and sequent = {
  (* antecedents:
  These include all definitions from module scope.
  The definitions are annotated as
  `Visible` or `Hidden` (see the component
  `visibility` of the constructor `Defn` of
  the type `hyp_` below).

  Proof obligations are sequents.
  Visible definitions in a proof obligation
  are expanded in `backends/prep.ml`.
  Hidden definitions remain in the
  sequent's context.
  *)
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
    (* declared identifier with:
      - name `hint.core`
      - arity `shape`
      - level `kind` (unspecified level if
        `kind` is `Unknown`)
      - domain bound `hdom`
    *)
  | Fresh of hint * shape * kind * hdom
    (* declared variable named `hint.core` *)
  | Flex of hint
    (* operator definition in module or `LET` scope *)
  | Defn of defn * wheredef * visibility * export
    (* theorem when it appears as hypothesis *)
  | Fact of expr * visibility * time

and hdom = Unbounded | Bounded of expr * visibility

and wheredef = Builtin | Proof of time | User

and export = Local | Export

and visibility = Visible | Hidden

and time = Now | Always | NotSet  (* this value
    exists because when we create facts,
    we need to wait for later normalization,
    in order to know if the terms are
    constants or not *)


let unditto (bounds: bounds): bounds =
    (* Repeat domain bounds where dittos occur.

    Caution: This function does *not* adjust
    the positional indices inside the duplicated
    bounds. This is correct for so long as
    these items remain inside a list of bounds,
    because all bounds attached to the same
    syntactic construct have the same context.

    However, as soon as these domain bounds
    are converted to hypotheses in a context
    (e.g., during syntax-tree traversal),
    they become declarations or definitions
    within a sequence of positional declarations.

    When this happens, any positional indices
    within the expressions of domain bounds
    need to be shifted according to their
    position.

    The function
    `Expr.Visit.hyps_of_bounds_unditto`
    applies this shifting.
    *)
    let is_dom = function
        | Domain _ -> ()
        | Ditto | No_domain -> assert false in
    let rec unditto out prevdom bs =
        let recurse b bs prevdom =
            let out = b :: out in
            unditto out prevdom bs in
        match bs with
        | (_, _, (Domain d as prevdom) as b) :: bs ->
            recurse b bs prevdom
        | (v, k, Ditto) :: bs ->
            is_dom prevdom;
            let b = (v, k, prevdom) in
            recurse b bs prevdom
        | (_, _, No_domain as b) :: bs ->
            recurse b bs prevdom
        | [] ->
            List.rev out in
    unditto [] No_domain bounds


let name_of_bound ((name, _, _): bound): hint =
    name


let names_of_bounds (bs: bounds): hints =
    let f (name, _, _) = name in
    List.map f bs


let string_of_bound
        ((name, _, _): bound): string =
    name.core


let strings_of_bounds (bs: bounds): string list =
    List.map string_of_bound bs


(* This function is used in module `E_deref`. *)
let bounds_of_variables
        (var_names: hints):
            bounds =
    let f name = (name, State, No_domain) in
    List.map f var_names


(* This function is used in module `E_deref`. *)
let bounds_of_parameters
        (param_names: (hint * shape) list):
            bounds =
    let f (name, _) = (name, Unknown, No_domain) in
    List.map f param_names


type meta = {
  hkind : hyp_kind ;
  name : string ;
}
and hyp_kind = Axiom | Hypothesis | Goal

let meta_prop = make "Expr.T.meta_prop"


type pat = expr list

let pattern_prop = make "Expr.T.pattern_prop"


let add_pats oe pats =
  match query oe pattern_prop with
  | Some pats' -> assign oe pattern_prop (pats @ pats')
  | None -> assign oe pattern_prop pats


let remove_pats oe =
  remove oe pattern_prop


let map_pats f oe =
  match query oe pattern_prop with
  | None -> oe
  | Some pats -> assign oe pattern_prop (List.map f pats)


let fold_pats f oe a =
  match query oe pattern_prop with
  | None -> a
  | Some pats -> List.fold_right f pats a


module type Name_type_sig =
sig
    type t
    val hint_of: t -> hint
end


module type Node_factory_sig =
(* The `make_*` functions create
syntax-tree nodes without
properties (read `Property.wrapped`).

This is the most common use case
for programmatic node creation,
because the created nodes do not
have a source location.

Annotating autogenerated nodes
with the source location of
the source element from which
they originate can cause confusion.

For cases where annotation of
autogenerated nodes is needed
(location information, or more
commonly expression levels,
type-synthesis information, etc),
the operator `$$` is useful.
*)
sig
    type t

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
        expr -> sel list -> expr
    val make_apply:
        expr -> expr list -> expr
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
        defn list -> expr ->
        expr
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
        t -> expr -> expr ->
        expr
    val make_setst:
        t -> expr ->
        expr -> expr
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
    val make_at:
        bool -> expr
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
        t -> kind -> expr ->
        bound
    val make_fresh:
        t -> kind -> hyp
    val make_bounded_fresh:
        t -> expr -> hyp
    val make_fresh_with_arity:
        t -> kind -> int -> hyp
end


module Make_node_factory(
    N: Name_type_sig) =
struct
    type t = N.t
    let hint_of x = N.hint_of x
    let string_of x = (hint_of x).core
    let key_to_string (a, b) = (
        string_of a, b)


    let make_ix
            (index: int):
                expr =
        let index_ = Ix index in
        noprops index_


    let make_opaque
            (name: t):
                expr =
        let name = string_of name in
        let opaque_ = Opaque name in
        noprops opaque_


    let make_internal
            (builtin_op:
                    Builtin.builtin):
                expr =
        noprops (Internal builtin_op)


    let make_arg
            (arg_name: t):
                (hint * shape) =
        (* Nullary argument. *)
        let arg_name = hint_of
            arg_name in
        let arg = (
            arg_name, Shape_expr) in
        arg


    let make_lambda
            (arg_names: t list)
            (expr: expr):
                expr =
        let arg_names = List.map
            make_arg arg_names in
        let lambda_ = Lambda (
            arg_names, expr) in
        noprops lambda_


    let make_def
            (op_name: t)
            (expr: expr):
                defn =
        let op_name = hint_of
            op_name in
        let op_defn_ = Operator (
            op_name, expr) in
        noprops op_defn_


    let make_def_with_args
            (op_name: t)
            (arg_names: t list)
            (expr: expr):
                defn =
        (* First-order definition.

        This function defines
        a first-order operator.
        Second-order operators
        can be defined by
        directly constructing
        the syntax-tree nodes
        that are needed for
        the definition.
        *)
        let lambda = make_lambda
            arg_names expr in
        let def = make_def
            op_name lambda in
        def


    let make_recursive_def
            (op_name: t)
            (shape: shape):
                defn =
        let op_name = hint_of
            op_name in
        let op_defn_ = Recursive (
            op_name, shape) in
        noprops op_defn_


    let make_sequent
            (context: ctx)
            (goal: expr):
                expr =
        let sequent = {
            context=context;
            active=goal} in
        let sq_ = Sequent sequent in
        noprops sq_


    let make_bang
            (expr: expr)
            (selectors: sel list):
                expr =
        let bang_ = Bang (
            expr, selectors) in
        noprops bang_


    let make_apply
            (op: expr)
            (args: expr list):
                expr =
        let apply_ = Apply (
            op, args) in
        noprops apply_


    let make_with
            (expr: expr)
            (method_: Method.t):
                expr =
        let with_ = With (
            expr, method_) in
        noprops with_


    let make_if
            (predicate: expr)
            (then_: expr)
            (else_: expr):
                expr =
        let if_node_ = If (
            predicate,
            then_,
            else_) in
        noprops if_node_


    let make_junction
            (op: bullet)
            (exprs: expr list):
                expr =
        let junction_ = List (
            op, exprs) in
        noprops junction_


    let make_disjunction
            (disjuncts: expr list):
                expr =
        make_junction Or disjuncts


    let make_conjunction
            (conjuncts: expr list):
                expr =
        make_junction And conjuncts


    let make_let
            (defs: defn list)
            (expr: expr):
                expr =
        let letin_ = Let (
            defs, expr) in
        noprops letin_


    let make_quantifier
            (quantifier: quantifier)
            (bounds: bounds)
            (predicate: expr):
                expr =
        let quant_ = Quant (
            quantifier,
            bounds,
            predicate) in
        noprops quant_


    let make_exists
            (bounds: bounds)
            (predicate: expr):
                expr =
        (* `\E <bounds>:  expr`. *)
        make_quantifier
            Exists bounds predicate


    let make_forall
            (bounds: bounds)
            (predicate: expr):
                expr =
        (* `\A <bounds>:  expr`. *)
        make_quantifier
            Forall bounds predicate


    let make_temporal_quantifier
            (quantifier: quantifier)
            (names: t list)
            (predicate: expr):
                expr =
        let names = List.map
            hint_of names in
        let tquant_ = Tquant (
            quantifier,
            names,
            predicate) in
        noprops tquant_


    let make_temporal_exists
            (names: t list)
            (predicate: expr):
                expr =
        make_temporal_quantifier
            Exists names predicate


    let make_temporal_forall
            (names: t list)
            (predicate: expr):
                expr =
        make_temporal_quantifier
            Forall names predicate


    let make_choose
            (name: t)
            (predicate: expr):
                expr =
        let name = hint_of name in
        let choose_ = Choose (
            name,
            None,
            predicate) in
        noprops choose_


    let make_bounded_choose
            (name: t)
            (bound: expr)
            (predicate: expr):
                expr =
        let name = hint_of name in
        let choose_ = Choose (
            name,
            Some bound,
            predicate) in
        noprops choose_


    let make_setst
            (name: t)
            (bound: expr)
            (predicate: expr):
                expr =
        let name = hint_of name in
        let setst_ = SetSt (
            name,
            bound,
            predicate) in
        noprops setst_


    let make_setof
            (expr: expr)
            (bounds: bounds):
                expr =
        let setof_ = SetOf (
            expr, bounds) in
        noprops setof_


    let make_setenum
            (exprs: expr list):
                expr =
        let setenum_ = SetEnum exprs in
        noprops setenum_


    let make_product
            (exprs: expr list):
                expr =
        let product_ = Product exprs in
        noprops product_


    let make_tuple
            (exprs: expr list):
                expr =
        let tuple_ = Tuple exprs in
        noprops tuple_


    let make_fcn
            (bounds: bounds)
            (value: expr):
                expr =
        let func_ = Fcn (
            bounds, value) in
        noprops func_


    let make_fcn_domain
            (func: expr):
                expr =
        (* Return `DOMAIN fcn`. *)
        let domain =
            make_internal DOMAIN in
        let domain_of_expr =
            make_apply domain [func] in
        domain_of_expr


    let make_fcn_app
            (func: expr)
            (arg: expr):
                expr =
        (* Return `func[arg]`.

        Relevant function:
            `make_fcn_app_commas`
        *)
        let fcn_app_ = FcnApp (
            func, [arg]) in
        noprops fcn_app_


    let make_fcn_app_commas
            (func: expr)
            (args: expr list):
                expr =
        (* Return `func[*args]`.

        The asterisk in `*args`
        denotes (syntactic) unpacking,
        and is notation borrowed
        from Python.

        Relevant function:
            `make_fcn_app`
        *)
        let fcn_app_ = FcnApp (
            func, args) in
        noprops fcn_app_


    let make_fcn_set
            (domain: expr)
            (range: expr):
                expr =
        let arrow_ = Arrow (
            domain, range) in
        noprops arrow_


    let make_record_set
            (key_domains:
                    (t * expr) list):
                expr =
        let key_domains = List.map
            key_to_string key_domains in
        let rect_ = Rect key_domains in
        noprops rect_


    let make_record
            (key_values:
                    (t * expr) list):
                expr =
        let key_values = List.map
            key_to_string key_values in
        let record_ = Record key_values in
        noprops record_


    let make_except
            (expr: expr)
            (updates:
                    exspec list):
                expr =
        let except_ = Except (
            expr, updates) in
        noprops except_


    let make_dot
            (expr: expr)
            (s: t):
                expr =
        let s = string_of s in
        let dot_ = Dot (expr, s) in
        noprops dot_


    let make_subscripted_action
            (modal_op: modal_op)
            (action: expr)
            (subscript: expr):
                expr =
        let sub_ = Sub (
            modal_op,
            action,
            subscript) in
        noprops sub_


    let make_square_action
            (action: expr)
            (subscript: expr):
                expr =
        make_subscripted_action
            Box action subscript


    let make_angle_action
            (action: expr)
            (subscript: expr):
                expr =
        make_subscripted_action
            Dia action subscript


    let make_temporal_subscripted
            (modal_op: modal_op)
            (action: expr)
            (subscript: expr):
                expr =
        let tsub_ = Tsub (
            modal_op,
            action,
            subscript) in
        noprops tsub_


    let make_subscripted_always
            (action: expr)
            (subscript: expr):
                expr =
        make_temporal_subscripted
            Box action subscript


    let make_subscripted_eventually
            (action: expr)
            (subscript: expr):
                expr =
        make_temporal_subscripted
            Dia action subscript


    let make_fairness
            (fairness_op: fairness_op)
            (action: expr)
            (subscript: expr):
                expr =
        let fair_ = Fair (
            fairness_op,
            action,
            subscript) in
        noprops fair_


    let make_weak_fairness
            (action: expr)
            (subscript: expr):
                expr =
        make_fairness
            Weak action subscript


    let make_strong_fairness
            (action: expr)
            (subscript: expr):
                expr =
        make_fairness
            Strong action subscript


    let make_case
            (guard_cases:
                (expr * expr) list)
            (other: expr option):
                expr =
        let case_node_ = Case (
            guard_cases,
            other) in
        noprops case_node_


    let make_string
            (s: t):
                expr =
        let s = string_of s in
        let s_ = String s in
        noprops s_


    let make_number
            (integral: t)
            (fractional: t):
                expr =
        let num_ = Num (
            string_of integral,
            string_of fractional) in
        noprops num_


    let make_at
            (b: bool):
                expr =
        noprops (At b)


    let make_parens
            (expr: expr)
            (form: pform):
                expr =
        let parens_ = Parens (
            expr, form) in
        noprops parens_


    let make_const_decl
            (name: t):
                bound =
        (* Return unbounded declaration.

        `name` is the identifier
        of the constant.
        *)
        let name = hint_of name in
        (name, Constant, No_domain)


    let make_const_decls
            (names: t list):
                bounds =
        List.map
            make_const_decl names


    let make_bounded_const_decl
            (name: t)
            (domain: expr):
                bound =
        let name = hint_of name in
        (name, Constant, Domain domain)


    let make_bounded_const_decls
            (name_domains:
                    (t * expr) list):
                bounds =
        let mk (name, domain) =
            make_bounded_const_decl
                name domain in
        List.map mk name_domains


    let make_param_decl
            (name: t):
                bound =
        let name = hint_of name in
        (name, Unknown, No_domain)


    let make_param_decls
            (names: t list):
                bounds =
        List.map
            make_param_decl names


    let make_unbounded
            (name: t)
            (kind: kind):
                bound =
        let name = hint_of name in
        (name, kind, No_domain)


    let make_bounded
            (name: t)
            (kind: kind)
            (bound: expr):
                bound =
        let name = hint_of name in
        (name, kind, Domain bound)


    let make_fresh
            (name: t)
            (kind: kind):
                hyp =
        (* Unbounded declaration.

        Related functions:
        - `make_bounded_fresh`
        - `make_fresh_with_arity`
        *)
        let name = hint_of name in
        let fresh = Fresh (
            name,
            Shape_expr,
            kind,
            Unbounded) in
        fresh @@ name


    let make_bounded_fresh
            (name: t)
            (domain: expr):
                hyp =
        (* With visible domain.

        Return declaration with
        visible domain.

        To create a declaration
        with a hidden domain-bound,
        use the relevant
        data constructors.

        The declared identifier
        is `CONSTANT`.

        Related function:
        - `make_fresh`
        - `make_fresh_with_arity`
        *)
        let name = hint_of name in
        let d = Bounded (
            domain, Visible) in
        let fresh = Fresh (
            name,
            Shape_expr,
            Constant,
            d) in
        fresh @@ name


    let make_fresh_with_arity
            (name: t)
            (kind: kind)
            (arity: int):
                hyp =
        (* Operator declaration.

        @param arity: int >= 0

        Related functions:
        - `make_fresh`
        - `make_bounded_fresh`
        *)
        if (arity < 0) then
            failwith (
                "expected " ^
                "arity >= 0, got " ^
                (string_of_int arity));
        let name = hint_of name in
        let fresh = Fresh (
            name,
            Shape_op arity,
            kind,
            Unbounded) in
        fresh @@ name
end


module From_string =
    Make_node_factory(
    struct
        type t = string
        let hint_of x = noprops x
    end)


module From_hint =
    Make_node_factory(
    struct
        type t = hint
        let hint_of x = x
    end)


(* context helper function *)
let get_val_from_id cx n =
    let item = Deque.nth
        ~backwards:true cx (n - 1) in
    match item with
    | Some e -> e
    | None -> failwith
        "unknown bound variable"


let name_of_ix
        (index: int)
        (cx: ctx):
            hint =
    (* Return name of positional index.

    @param index: positional index `n >= 1`
    @param cx: context, with length `>= n`
    @return: name that corresponds to
        `index` in the context `cx`
    *)
    if index < 1 then
        failwith (
            "positional index `= " ^
            (string_of_int index) ^
            " < 1`");
    assert (index >= 1);
    let hyp = get_val_from_id cx index in
    match hyp.core with
    | Flex name
    | Fresh (name, _, _, _) -> name
    | Defn (df, _, _, _) -> begin
        match df.core with
        | Operator (name, _)
        | Bpragma (name, _, _)
        | Instance (name, _) -> name
        | Recursive (name, _) ->
            failwith "`RECURSIVE`\
                declaration found"
        end
    | Fact _ ->
        failwith "Found \
            positional index \
            that refers to Fact."


let hyp_hint h = match h.core with
    | Fresh (nm, _, _, _)
    | Flex nm
    | Defn ({core =
              Operator (nm, _)
            | Instance (nm, _)
            | Bpragma(nm,_,_)
            | Recursive (nm, _)},
            _, _, _)
        -> nm
    | Fact (_, _,_) -> "??? FACT ???" %% []

let hyp_name h = (hyp_hint h).core


let visibility_to_string = function
    | Visible -> "visible"
    | Hidden -> "hidden"


let visibility_of_domain = function
    | Bounded (_, visibility) ->
        visibility_to_string visibility
    | Unbounded -> "no domain"


let describe_domain_bound = function
    | Bounded (_, visibility) ->
        let visible = visibility_to_string
            visibility in
        "with " ^ visible ^ " domain-bound"
    | Unbounded -> "without domain-bound"


let print_cx cx =
    (* Print the hypotheses of context `cx`. *)
    print_string "\nContext of sequent \
        (hypotheses):\n";
    let print_hyp i hyp =
        let idx = string_of_int i in
        print_string ("\nHypothesis with index " ^
            idx ^ " :\n");
        let msg = match hyp.core with
            | Flex name ->
                "Variable `" ^ name.core ^ "`\n"
            | Fresh (name, arity, kind, dom) ->
                let visible = describe_domain_bound dom in
                ("Constant operator `" ^ name.core ^
                 "` (" ^ visible ^ ")\n")
            | Defn (df, _, visibility, _) ->
                let visible = visibility_to_string
                    visibility in
                let prefix = match df.core with
                | Operator (name, expr) ->
                    "Defined operator `" ^ name.core
                | Bpragma (name, _, _) ->
                    "Backend pragma `" ^ name.core
                | Instance (name, _) ->
                    "INSTANCE `" ^ name.core
                | Recursive (name, _) ->
                    "`RECURSIVE` declaration of `" ^
                    name.core
                in
                prefix ^ "` (" ^ visible ^ ")\n"
            | Fact (expr, visibility, _) ->
                let visible = visibility_to_string
                    visibility in
                "Fact (" ^ visible ^ ")\n"
            in
        print_string msg
        in
    Deque.iter print_hyp cx


let cx_front cx n =
    (* Omit `n` last elements of deque `cx`. *)
    let k = (Deque.size cx) - n in
    let new_cx = Deque.first_n cx k in
    new_cx


let scx_front scx n =
    (* Omit `n` last elements from deque `snd scx`.

    Returns `scx` with the `n` last elements
    omitted from `snd scx`.
    *)
    let cx = snd scx in
    let new_cx = cx_front cx n in
    let new_scx = (fst scx, new_cx) in
    new_scx


let find_hyp_named
        (cx: hyp Deque.dq)
        (name: string): (int * hyp) =
    (* Return the depth in the context `cx` of
    the hypothesis with `name`, and
    the hypothesis expression.
    *)
    assert (name <> "??? FACT ???");
    let name_test hyp = (name = (hyp_name hyp)) in
    let pair = Deque.find
        ~backwards:true cx name_test in
    let pair = Option.get pair in
    let (depth, expr) = pair in
    (depth, expr)


let expr_locus expr =
    match Util.query_locus expr with
    | None -> None
    | Some loc ->
        let loc_str = Loc.string_of_locus
            ~cap:true loc in
        Some loc_str


let format_locus expr =
    match (expr_locus expr) with
    | None -> "<unknown location>"
    | Some loc_str -> loc_str


let exprify_sequent sq =
  if Deque.null sq.context
  then sq.active.core
  else Sequent sq


let shape_to_arity (shape: shape): int =
    (* Return arity that corresponds to `shape`.

    The arity is of an operator.
    *)
    let arity = match shape with
        | Shape_expr -> 0
        | Shape_op arity ->
            assert (arity >= 1);
            arity
        in
    assert (arity >= 0);
    arity


type hyp_numbers = {
    n_variables: int;
    n_constants: int;
    n_visible_defs: int;
    n_hidden_defs: int;
    n_visible_facts: int;
    n_hidden_facts: int;
    visible_definition_names: string list;
    hidden_definition_names: string list;
    visible_fact_names: expr list;
    hidden_fact_names: expr list}


let rec number_of_hyp (hyps: ctx) =
    let n_variables = ref 0 in
    let n_constants = ref 0 in
    let n_visible_defs = ref 0 in
    let n_hidden_defs = ref 0 in
    let n_visible_facts = ref 0 in
    let n_hidden_facts = ref 0 in
    let visible_definition_names = ref [] in
    let hidden_definition_names = ref [] in
    let visible_fact_names = ref [] in
    let hidden_fact_names = ref [] in
    let rec recurse hyps =
        begin match Deque.front hyps with
        | None -> ()
        | Some (h, hs) -> begin match h.core with
            | Fresh _ -> incr n_constants
            | Flex _ -> incr n_variables
            | Defn (
                    {core=Operator (name, _)},
                    _, Visible, _)
            | Defn (
                    {core=Bpragma (name, _, _)},
                    _, Visible, _) ->
                incr n_visible_defs;
                visible_definition_names :=
                    name.core
                    :: !visible_definition_names
            | Defn (
                    {core=Operator (name, _)},
                    _, Hidden, _)
            | Defn (
                    {core=Bpragma (name, _, _)},
                    _, Hidden, _) ->
                incr n_hidden_defs;
                hidden_definition_names :=
                    name.core
                    :: !hidden_definition_names
            | Fact (expr, Hidden, _) ->
                incr n_hidden_facts;
                visible_fact_names :=
                    expr :: !visible_fact_names
            | Fact (expr, Visible, _) ->
                incr n_visible_facts;
                hidden_fact_names :=
                    expr :: !hidden_fact_names
            | _ -> assert false
            end;
            recurse hs
        end in
    recurse hyps;
    let r = {
        n_variables=
            !n_variables;
        n_constants=
            !n_constants;
        n_visible_defs=
            !n_visible_defs;
        n_hidden_defs=
            !n_hidden_defs;
        n_visible_facts=
            !n_visible_facts;
        n_hidden_facts=
            !n_hidden_facts;
        visible_definition_names=
            !visible_definition_names;
        hidden_definition_names=
            !hidden_definition_names;
        visible_fact_names=
            !visible_fact_names;
        hidden_fact_names=
            !hidden_fact_names}
    in
    r


let sequent_stats (sq: sequent) =
    (* Count and print numbers of hypotheses.

    Each kind of hypothesis is counted
    separately.
    *)
    let n_hyp = Deque.size sq.context in
    let nums = number_of_hyp sq.context in
    let msg = (
        "\nNumber of sequent hypotheses: " ^
            (string_of_int n_hyp) ^
        "\nNumber of constants: " ^
            (string_of_int nums.n_constants) ^
        "\nNumber of variables: " ^
            (string_of_int nums.n_variables) ^
        "\nNumber of visible definitions: " ^
            (string_of_int nums.n_visible_defs) ^
        "\nNumber of hidden definitions: " ^
            (string_of_int nums.n_hidden_defs) ^
        "\nNumber of visible facts: " ^
            (string_of_int nums.n_visible_facts) ^
        "\nNumber of hidden facts: " ^
            (string_of_int nums.n_hidden_facts) ^
        "\n\n" ^
        "\nVisible definition names:\n" ^
            (String.concat "\n"
             nums.visible_definition_names) ^
        "\nHidden definition names:\n" ^
            (String.concat "\n"
             nums.hidden_definition_names) ^
        "\nVisible fact names:\n")
        in
    Util.printf ~prefix:"[INFO]: " "%s" msg;
    (*
    let print_fact e =
        let print = Expr.Fmt.pp_print_expr in
        let cx = (Deque.empty, Ctx.dot) in
        let fmt = Format.std_formatter in
        print cx fmt e
        in
    List.iter print_fact nums.visible_fact_names;
    print_string "Hidden fact names:\n";
    List.iter print_fact nums.hidden_fact_names; *)
    n_hyp


let enabledaxioms: bool pfuncs =
  Property.make "Module.Elab.enabledaxioms"
let has_enabledaxioms x = Property.has
    x enabledaxioms
let get_enabledaxioms x = Property.get
    x enabledaxioms
