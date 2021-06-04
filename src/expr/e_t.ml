(*
 * expressions
 *
 *
 * Copyright (C) 2008-2019  INRIA and Microsoft Corporation
 *)

open Ext
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
    (* de Bruijn index *)
  | Ix of int
    (* identifier name *)
  | Opaque of string
    (* builtin operator *)
  | Internal of Builtin.builtin
    (* `LAMBDA` and
    signatures of operator definitions *)
  | Lambda of (hint * shape) list * expr
    (* sequents (`ASSUME`/`PROVE` with definitions from
    module scope) *)
  | Sequent of sequent
    (* unified module and subexpression references (Foo!Op) *)
  | Bang of expr * sel list
    (* ordinary TLA+ expressions *)
    (* operator application `Op(arg1, arg2)` *)
  | Apply of expr * expr list
    (* Expression annotated with prover directive. *)
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
  | Tquant of quantifier * hint list * expr
    (* `CHOOSE` *)
  | Choose of hint * expr option * expr
    (* `{x \in S:  P(x)}`
    axiom scheme of separation

    Section 16.1.6 on pages 299--301 of the book "Specifying Systems",
    specifically page 301
    *)
  | SetSt of hint * expr * expr
    (* `{f(x):  x \in S}`
    axiom scheme of replacement

    Section 16.1.6 on pages 299--301 of the book "Specifying Systems",
    specifically page 301
    *)
  | SetOf of expr * bounds
    (* `{1, 2}`
    set enumeration

    Section 16.1.6 on pages 299--301 of the book "Specifying Systems",
    specifically page 300
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
    (* Subscripted (action) expressions:  `[A]_v` and `<< A >>_v` *)
  | Sub of modal_op * expr * expr
    (* Temporal subscripted expressions:  `[][A]_v` and `<><< A >>_v` *)
  | Tsub of modal_op * expr * expr
    (* `WF_` and `SF_` *)
  | Fair of fairness_op * expr * expr
    (* `CASE` *)
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

(** Definitions

- Used in LET scope.
- Used within Defn when in antecedents.
*)
and defn = defn_ wrapped
and defn_ =
    (* recursive operator definition
    Results by expanding in the function `hyps_of_modunit`
    a `RECURSIVE` section represented by `Module.T.Recursives`.
    *)
  | Recursive of hint * shape
    (*
    operator definition:
    - name `hint`
    - body `expr`:
      - if arity is <_, ... >, then a `Lambda (args, expr)`, with:
        - `args`: the signature of the operator definition
        - `expr`: the expression of the body of the operator definition.
      - if arity is _, then the expression of the definition body.
    *)
  | Operator of hint * expr
    (* parameter substitution for instantiation *)
  | Instance of hint * instance
  | Bpragma of hint * expr * ((hint * backend_args) list list)

(** Instance *)
and instance = {
  (** arguments of the statement `INSTANCE`, for example:

    let wrap (x: string): hint = noprops x in
    List.map wrap ["x"; "y"]
  *)
  inst_args : hint list ;

  (** name of the instantiated module *)
  inst_mod  : string ;

  (** substitution defined by the statement `INSTANCE`, for example:

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

(** The [sequent] type represents (a generalisation of) TLA+
    ASSUME/PROVE forms *)
and sequent = {
  (** antecedents:
  These include all definitions from module scope.
  The definitions are annotated as `Visible` or `Hidden` (see the component
  `visibility` of the constructor `Defn` of the type `hyp_` below).
  Proof obligations are sequents. Visible definitions in a proof obligation are
  expanded in `backends/prep.ml`. Hidden definitions remain in the
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
      - level `kind` (unspecified level if `kind` is `Unknown`)
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

and time = Now | Always | NotSet (* this value exists because when we create
facts, we need to wait for later normalization in order to know if the terms are
constants or not *)

(* context helper function *)
let get_val_from_id cx n = match Deque.nth ~backwards:true cx (n - 1) with
| Some e -> e
| None -> failwith "unknown bound variable"

let hyp_name h = match h.core with
  | Fresh (nm, _, _, _)
  | Flex nm
  | Defn ({core = Operator (nm, _) | Instance (nm, _)
                  | Bpragma(nm,_,_) | Recursive (nm, _)},
          _, _, _)
  -> nm.core
  | Fact (_, _,_) -> "_"


let visibility_to_string = function
    | Visible -> "visible"
    | Hidden -> "hidden"


let print_cx cx =
    (* Print the hypotheses of context `cx`. *)
    print_string "\nContext of sequent (hypotheses):\n";
    let print_hyp i hyp =
        let idx = string_of_int i in
        print_string ("\nHypothesis with index " ^ idx ^ " :\n");
        let msg = match hyp.core with
            | Flex name ->
                "Variable `" ^ name.core ^ "`\n"
            | Fresh (name, arity, kind, dom) ->
                "Constant operator `" ^ name.core ^ "`\n"
            | Defn (df, _, visibility, _) ->
                let name = match df.core with
                    | Operator (name, expr) -> name
                    | Bpragma (name, expr, backend_args) -> name
                    | Instance (name, instance) -> name
                    | Recursive (name, arity) -> name
                    in
                let visible = visibility_to_string visibility in
                "Defined operator `" ^ name.core ^ "` (" ^ visible ^ ")\n"
            | Fact (expr, visibility, _) ->
                let visible = visibility_to_string visibility in
                "Fact (" ^ visible ^ ")\n"
            in
        print_string msg
        in
    Deque.iter print_hyp cx


let cx_front cx n =
    (* front of queue `cx` omitting the `n` last elements. *)
    let k = (Deque.size cx) - n in
    let new_cx = Deque.first_n cx k in
    new_cx


let scx_front scx n =
    (* `scx` with `n` last elements omitted from `snd scx`. *)
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
    let name_test hyp = (name = (hyp_name hyp)) in
    let pair = Deque.find ~backwards:true cx name_test in
    let pair = Option.get pair in
    let (depth, expr) = pair in
    (depth, expr)


let expr_locus expr = match Util.query_locus expr with
    | None -> None
    | Some loc ->
        let loc_str = Loc.string_of_locus ~cap:true loc in
        Some loc_str


let format_locus expr = match (expr_locus expr) with
    | None -> "<unknown location>"
    | Some loc_str -> loc_str


let exprify_sequent sq =
  if Deque.null sq.context
  then sq.active.core
  else Sequent sq


let shape_to_arity (shape: shape): int =
    (* Return operator arity that corresponds to `shape`. *)
    let arity = match shape with
        | Shape_expr -> 0
        | Shape_op arity -> assert (arity >= 1); arity
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
            | Defn ({core=Operator (name, _)}, _, Visible, _)
            | Defn ({core=Bpragma (name, _, _)}, _, Visible, _) ->
                incr n_visible_defs;
                visible_definition_names :=
                    name.core :: !visible_definition_names
            | Defn ({core=Operator (name, _)}, _, Hidden, _)
            | Defn ({core=Bpragma (name, _, _)}, _, Hidden, _) ->
                incr n_hidden_defs;
                hidden_definition_names :=
                    name.core :: !hidden_definition_names
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
        n_variables=(!n_variables);
        n_constants=(!n_constants);
        n_visible_defs=(!n_visible_defs);
        n_hidden_defs=(!n_hidden_defs);
        n_visible_facts=(!n_visible_facts);
        n_hidden_facts=(!n_hidden_facts);
        visible_definition_names=(!visible_definition_names);
        hidden_definition_names=(!hidden_definition_names);
        visible_fact_names=(!visible_fact_names);
        hidden_fact_names=(!hidden_fact_names)}
    in
    r


let sequent_stats (sq: sequent) =
    (* Count and print number of each kind of hypothesis. *)
    let n_hyp = Deque.size sq.context in
    let nums = number_of_hyp sq.context in
    let msg = (
        "\nNumber of sequent hypotheses: " ^ (string_of_int n_hyp) ^
        "\nNumber of constants: " ^ (string_of_int nums.n_constants) ^
        "\nNumber of variables: " ^ (string_of_int nums.n_variables) ^
        "\nNumber of visible definitions: " ^
            (string_of_int nums.n_visible_defs) ^
        "\nNumber of hidden definitions: " ^
            (string_of_int nums.n_hidden_defs) ^
        "\nNumber of visible facts: " ^
            (string_of_int nums.n_visible_facts) ^
        "\nNumber of hidden facts: " ^ (string_of_int nums.n_hidden_facts) ^
        "\n\n" ^
        "\nVisible definition names:\n" ^
        (String.concat "\n" nums.visible_definition_names) ^
        "\nHidden definition names:\n" ^
        (String.concat "\n" nums.hidden_definition_names) ^
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

let enabledaxioms : bool pfuncs =
  Property.make "Module.Elab.enabledaxioms"
let has_enabledaxioms x = Property.has x enabledaxioms
let get_enabledaxioms x = Property.get x enabledaxioms
