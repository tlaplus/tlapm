(** This module converts SANY's abstract syntax tree (AST) into TLAPM's AST.
    The two trees are quite different. SANY makes great use of globally unique
    identifiers to reference one entity from another; for example, when the
    symbol "x" is declared in a module, it is given a unique integer ID, and
    all subsequent references to "x" use that ID. TLAPM, in contrast, uses De
    Bruijn indices to represent variable references and has no equivalent to
    a global symbol table. TLAPM also makes greater use of variants, as would
    be expected in OCaml code; SANY is written in Java, so has a greater focus
    on abstracting different AST nodes into a single AST node type. Nowhere is
    this more apparent than in SANY's OpApplNode type, which is used for
    everything from simple expressions like 1 + 3 to complex constructs like
    \A x, y, z \in S : P.

    Much of the challenge of this module, in addition to the sheer number of
    TLA+ syntax node types it has to convert, is the difficulty in mapping
    the information in each SANY AST node to the fields expected in each
    TLAPM node type. Often, TLAPM fields have no obvious use at this point in
    the parsing process; they are clearly set up to be used later on during
    proof elaboration or level-checking. TLAPM also wraps many AST nodes with
    a generic key-value map used to store all kinds of things, most
    prominently location & level information. SANY does not have an
    equivalent, and prefers to store such information directly as fields in
    each AST node. Internally, SANY actually has two different AST formats:
    a very low-level one with close conformance to TLA+ syntax, and a more
    abstract which is presented to us here. Thus the SANY AST has already
    been processed significantly, and we are translating it to a form that is
    comparatively much rougher & earlier in the parse process.

    There are two places in this conversion code where we revert to actually
    just parsing the underlying "raw" TLA+ syntax from SANY's AST: proof names
    and references to named instanced modules. We need to parse proof names
    because we have to extract the proof level, which TLAPM expects as some
    metadata attached to proof objects. SANY could possibly be modified to
    export proof level data with its XML, but for now we just extract the
    level from the proof name. We need to parse references to named instanced
    modules because if a module is imported with M == INSTANCE Modname, all
    definitions from Modname will be inlined in the importing module while
    prefixed like M!Defname. This is mostly fine because TLAPM runs its own
    De Bruijn-index-based name resolution algorithm, except for the case where
    Defname == OtherDefname. Then when analyzing M!Defname, TLAPM will search
    for OtherDefname instead of M!OtherDefname. Thus we need to "undo" the
    SANY name resolution process further by filtering out all inlined operators
    and breaking references like M!Defname down into [M; Defname] components.
    We crudely do this by splitting on !, making allowances for the possibility
    that the !! operator is used.

    Given these challenges, much SANY information such as identifier reference
    IDs and levels are attached as metadata to TLAPM AST nodes for use later
    on: not as the basis for final calculations, but rather to cross-check
    them with TLAPM's own internal calculations. In particular, the difference
    between UIDs and De Bruijn indices is so large that it is not feasible to
    directly translate the logic without significant risk of introducing bugs.
    Instead, the conversion to De Bruijn indices is modified to check that the
    calculation matches the original UID-based reference, and error if not.
    While this does not alleviate TLAPM maintenance costs as much as hoped,
    it at least provides a strong safeguard against bugs. Future work can
    possibly at least remove level-checking from TLAPM.
*)

open Property;;
open Module.T;;
open Expr.T;;
open Proof.T;;
open Util;;

type language_feature =
  | RecursiveOperator
  | InstanceProofStep
  | Subexpression

exception Unsupported_language_feature of Loc.locus option * language_feature

type conversion_failure_kind =
  | NotYetImplemented
  | InvalidBoundsOrOperands

exception Conversion_failure of conversion_failure_kind * string option * string

(** Utility function constructing & raising an exception for when conversion
    of a TLA+ language feature is not yet implemented, although is planned to
    be; Unsupported_language_feature is used when support is not currently
    planned although could be added in the future.
*)
let todo (category : string) (msg : string) (loc : Xml.location option) : 'a =
  raise (Conversion_failure (NotYetImplemented, Option.map Xml.show_location loc, Printf.sprintf "%s not yet implemented: %s" category msg))

(** Utility function constructing & raising an exception for when conversion
    of a TLA+ language construct fails due to invalid bounds or operands from
    SANY's parse output. This can broadly be viewed as a way to account for
    the projection from Java's type system to OCaml's variants, in that Java
    allows representation of invalid data (for example: more than one arg to
    existential quantification) which is occluded by OCaml's variants.
*)
let conversion_failure (msg : string) (loc : Xml.location option) : 'a =
  raise (Conversion_failure (InvalidBoundsOrOperands, Option.map Xml.show_location loc, msg))

(** A module-global table of SANY AST entities, indexed by UID.
*)
let entries : Xml.entry_kind Coll.Im.t ref = ref Coll.Im.empty

(** Converts SANY's location format to TLAPM's, for attachment to node
    metadata. Since the SANY location does not include data for byte offsets
    from beginning of file, we set those to 0 here.
*)
let convert_location ({column = (col_start, col_finish); line = (line_start, line_finish); filename} : Xml.location) : Loc.locus = {
  start = Actual {
    line = line_start;
    bol = 0;
    col = col_start;
  };
  stop = Actual {
    line = line_finish;
    bol = 0;
    col = col_finish;
  };
  file = filename ^ ".tla";
}

(** An attempt to reduce code duplication between tuple & non-tuple bounds by
    wrapping them in a variant.
*)
type bounds_kind =
  | Tuply of tuply_bounds
  | NonTuply of bounds

(** Wraps the given proof step with its name in the metadata.
*)
let attach_proof_step_name (proof_name : stepno) (step : 'a) : 'a =
  assign step Props.step proof_name

(** Wrap the given object in location data.
    TODO: also wrap with level data.
*)
let attach_props (props : Xml.node) (value : 'a) : 'a wrapped =
  match props.location with
  | Some loc -> Util.locate value (convert_location loc)
  | None -> noprops value

(** Look up the given ref in the global entries table, failing if not found.
*)
let resolve_ref (node : Xml.node) (uid : int) : Xml.entry =
  match Coll.Im.find_opt uid !entries with
  | Some kind -> {uid; kind}
  | None -> conversion_failure ("Unresolved reference to entry UID: " ^ string_of_int uid) node.location

(** A typed version of resolve_ref for module nodes.
*)
let resolve_module_node (node : Xml.node) (uid : int) : Xml.module_node =
  match (resolve_ref node uid).kind with
  | ModuleNode mule -> mule
  | _ -> conversion_failure ("Expected module node for UID: " ^ string_of_int uid) node.location

(** A typed version of resolve_ref for operator declaration nodes.
*)
let resolve_op_decl_node (node : Xml.node) (uid : int) : Xml.op_decl_node =
  match (resolve_ref node uid).kind with
  | OpDeclNode odn -> odn
  | _ -> conversion_failure ("Expected operator declaration node for UID: " ^ string_of_int uid) node.location

(** A typed version of resolve_ref for user-defined operators.
*)
let resolve_user_defined_op_kind (node : Xml.node) (uid : int) : Xml.user_defined_op_kind =
  match (resolve_ref node uid).kind with
  | UserDefinedOpKind udok -> udok
  | _ -> conversion_failure ("Expected user defined operator for UID: " ^ string_of_int uid) node.location

(** A typed version of resolve_ref for operator parameter nodes.
*)
let resolve_formal_param_node (node : Xml.node) (uid : int) : Xml.formal_param_node =
  match (resolve_ref node uid).kind with
  | Xml.FormalParamNode xml -> xml
  | _ -> conversion_failure ("Expected formal parameter node for UID: " ^ string_of_int uid) node.location

(** A typed version of resolve_ref for theorem definition nodes.
*)
let resolve_theorem_def_node (node : Xml.node) (uid : int) : Xml.theorem_def_node =
  match (resolve_ref node uid).kind with
  | TheoremDefNode xml -> xml
  | _ -> conversion_failure ("Expected theorem definition node for UID: " ^ string_of_int uid) node.location

(** A typed version of resolve_ref for assume definition nodes.
*)
let resolve_assume_def_node (node : Xml.node) (uid : int) : Xml.assume_def_node =
  match (resolve_ref node uid).kind with
  | AssumeDefNode xml -> xml
  | _ -> conversion_failure ("Expected assume definition node for UID: " ^ string_of_int uid) node.location

(** A typed version of resolve_ref for theorem nodes.
*)
let resolve_theorem_node (node : Xml.node) (uid : int) : Xml.theorem_node =
  match (resolve_ref node uid).kind with
  | TheoremNode xml -> xml
  | _ -> conversion_failure ("Expected theorem node for UID: " ^ string_of_int uid) node.location

(** A typed version of resolve_ref for bound symbols.
*)
let resolve_bound_symbol (node : Xml.node) (uid : int) : hint =
  match (resolve_ref node uid).kind with
  | FormalParamNode ({arity = 0} as xml) -> attach_props xml.node xml.name
  | FormalParamNode _ -> conversion_failure ("Bound symbol cannot be an operator: " ^ string_of_int uid) node.location
  | _ -> conversion_failure ("Unresolved formal parameter node UID: " ^ string_of_int uid) node.location

(** Resolves definitions referenced in BY proofs or USE/HIDE statements.
*)
let resolve_def (node : Xml.node) (ref : int) : use_def wrapped =
    match (resolve_ref node ref).kind with
    | UserDefinedOpKind op -> Dvar op.name |> attach_props op.node
    | TheoremDefNode thm -> Dvar thm.name |> attach_props thm.node
    | other -> conversion_failure ("Invalid definition reference in BY proof: " ^ (Xml.show_entry_kind other)) node.location

(** Predicate for quickly checking whether a given UID corresponds to the
    given built-in operator.
*)
let is_builtin_op (node : Xml.node) (uid : int) (op : Xml.built_in_operator) : bool =
  match (resolve_ref node uid).kind with
  | BuiltInKind {operator} when operator = op -> true
  | _ -> false

(** Unboxes the Leibniz param into a formal param node and converts it into
    the form usually (but not always; see labels) used within TLAPM.
*)
let convert_leibniz_param_node (node : Xml.node) ({ref} : Xml.leibniz_param) : (hint * shape) =
  let fpn = resolve_formal_param_node node ref in
  attach_props fpn.node fpn.name,
  match fpn.arity with
  | 0 -> Shape_expr
  | n -> Shape_op n

(** An OpApplNode's operands can be either expressions or operator arguments.
    Often we only want them to be expressions. This function coerces the list
    items into expressions, raising an error if they are operators.
*)
let as_expr_ls (name : string) (loc : Xml.location option) (operands : Xml.expr_or_op_arg list) : Xml.expression list =
  let exprs = List.filter_map
    (fun (operand : Xml.expr_or_op_arg) -> match operand with Expression e -> Some e | _ -> None)
    operands
  in if List.length exprs <> List.length operands
  then conversion_failure (Format.sprintf "Expected all operands to be expressions in %s" name) loc
  else exprs

(** Several places require special handling of the last element of a list,
    for example proof steps which end in a QED and CASE pairs which end
    (possibly) in an OTHER statement. This utility function helps with that.
*)
let split_last_ls (node : Xml.node) (ls : 'a list) : 'a list * 'a =
  match List.rev ls with
  | [] -> conversion_failure "Cannot get last element of empty list" node.location
  | hd :: tl -> (List.rev tl, hd)

(** Utility function to convert a list of operands to a list of expression pairs.
*)
let as_pair (node : Xml.node) (operand : Xml.expr_or_op_arg) : (Xml.expression * Xml.expression) =
  match operand with
  | Expression OpApplNode {operator; bound_symbols = []; operands = [Expression left; Expression right]} -> (
    match (resolve_ref node operator).kind with
    | BuiltInKind {operator = Pair} -> (left, right)
    | _ -> conversion_failure "Expected pair of expressions" node.location
  ) | _ -> conversion_failure "Expected pair of expressions" node.location

(** Converts a SANY built-in operator to a TLAPM built-in operator. This is
    only defined for a subset of the operators that SANY considers built-in,
    and not all operators that TLAPM considers built-in are represented in
    the SANY built-in operators. TLAPM also considers all the standard module
    operators to be built-in operators.
*)
let sany_to_tlapm_builtin (node : Xml.node) (builtin : Xml.built_in_operator) : Builtin.builtin =
  match builtin with
  (* Reserved words *)
  | TRUE -> Builtin.TRUE
  | FALSE -> Builtin.FALSE
  | BOOLEAN -> Builtin.BOOLEAN
  | STRING -> Builtin.STRING
  (* Prefix operators *)
  | LogicalNegation -> Builtin.Neg
  | UNION -> Builtin.UNION
  | SUBSET -> Builtin.SUBSET
  | DOMAIN -> Builtin.DOMAIN
  | ENABLED -> Builtin.ENABLED
  | UNCHANGED -> Builtin.UNCHANGED
  | Always -> (Builtin.Box false) (* TODO: figure out meaning of false parameter *)
  | Eventually -> Builtin.Diamond
  (* Postfix operators *)
  | Prime -> Builtin.Prime
  (* Infix operators *)
  | SetIn -> Builtin.Mem
  | SetNotIn -> Builtin.Notmem
  | Implies -> Builtin.Implies
  | Equivalent -> Builtin.Equiv
  | Conjunction -> Builtin.Conj
  | Disjunction -> Builtin.Disj
  | Equals -> Builtin.Eq
  | NotEquals -> Builtin.Neq
  | SetMinus -> Builtin.Setminus
  | Union -> Builtin.Cup
  | Intersect -> Builtin.Cap
  | SubsetEq -> Builtin.Subseteq
  | LeadsTo -> Builtin.Leadsto
  | ActionComposition -> Builtin.Cdot
  | PlusArrow -> Builtin.Actplus
  | _ -> conversion_failure ("SANY built-in operator cannot be translated to TLAPM built-in operator: " ^ Xml.show_built_in_operator builtin) node.location

(** Conversion of application of all traditional built-in operators like = or
    \cup but also things like CHOOSE and \A which one would ordinarily not
    view as built-in operators.
*)
let rec convert_built_in_op_appl (apply : Xml.op_appl_node) (op : Xml.built_in_kind) : Expr.T.expr =
  (** TLAPM has a specific set of operators it considers "built in" which is
      different from the set that SANY consideres "built-in"; this function
      constructs operators for the TLAPM built-in operator set.
  *)
  let mk (builtin : Builtin.builtin) : Expr.T.expr = Apply (
      Internal builtin |> attach_props op.node,
      apply.operands |> as_expr_ls (Builtin.builtin_to_string builtin) apply.node.location |> List.map convert_expression
    ) |> attach_props apply.node
  in match op.operator with
  (* Reserved words *)
  | TRUE -> mk Builtin.TRUE
  | FALSE -> mk Builtin.FALSE
  | BOOLEAN -> mk Builtin.BOOLEAN
  | STRING -> mk Builtin.STRING
  (* Prefix operators *)
  | LogicalNegation -> mk Builtin.Neg
  | UNION -> mk Builtin.UNION
  | SUBSET -> mk Builtin.SUBSET
  | DOMAIN -> mk Builtin.DOMAIN
  | ENABLED -> mk Builtin.ENABLED
  | UNCHANGED -> mk Builtin.UNCHANGED
  | Always -> mk (Builtin.Box false) (* TODO: figure out meaning of false parameter *)
  | Eventually -> mk Builtin.Diamond
  (* Postfix operators *)
  | Prime -> mk Builtin.Prime
  (* Infix operators *)
  | SetIn -> mk Builtin.Mem
  | SetNotIn -> mk Builtin.Notmem
  | Implies -> mk Builtin.Implies
  | Equivalent -> mk Builtin.Equiv
  | Conjunction -> mk Builtin.Conj
  | Disjunction -> mk Builtin.Disj
  | Equals -> mk Builtin.Eq
  | NotEquals -> mk Builtin.Neq
  | SetMinus -> mk Builtin.Setminus
  | Union -> mk Builtin.Cup
  | Intersect -> mk Builtin.Cap
  | SubsetEq -> mk Builtin.Subseteq
  | LeadsTo -> mk Builtin.Leadsto
  | ActionComposition -> mk Builtin.Cdot
  | PlusArrow -> mk Builtin.Actplus
  (* Language operators *)
  | FiniteSetLiteral -> SetEnum (
      apply.operands |> as_expr_ls "FiniteSetLiteral" apply.node.location |> List.map convert_expression
    ) |> attach_props apply.node
  | TupleLiteral -> Tuple (
      apply.operands |> as_expr_ls "TupleLiteral" apply.node.location |> List.map convert_expression
    ) |> attach_props apply.node
  | ConjunctionList -> List (
      And, apply.operands |> as_expr_ls "ConjunctionList" apply.node.location |> List.map convert_expression
    ) |> attach_props apply.node
  | DisjunctionList -> List (
      Or, apply.operands |> as_expr_ls "DisjunctionList" apply.node.location |> List.map convert_expression
    ) |> attach_props apply.node
  | CartesianProduct -> Product (
      apply.operands |> as_expr_ls "CartesianProduct" apply.node.location |> List.map convert_expression
    ) |> attach_props apply.node
    | WeakFairness -> convert_fairness Weak apply
    | StrongFairness -> convert_fairness Strong apply
    | BoundedChoose -> convert_choose apply
    | UnboundedChoose -> convert_choose apply
    | ActionOrStutter -> convert_action_expr Box apply
    | ActionNoStutter -> convert_action_expr Dia apply
    | BoundedExists -> convert_quantification Exists apply
    | BoundedForAll -> convert_quantification Forall apply
    | UnboundedExists -> convert_quantification Exists apply
    | UnboundedForAll -> convert_quantification Forall apply
    | TemporalExists -> convert_temporal_quantification Exists apply
    | TemporalForAll -> convert_temporal_quantification Forall apply
    | FiniteSetMap -> convert_set_map apply
    | FiniteSetFilter -> convert_set_filter apply
    | FunctionSet -> convert_function_set apply
    | FunctionConstructor -> convert_function_constructor apply
    | FunctionDefinition -> convert_function_constructor apply
    | RecursiveFunctionDefinition -> convert_recursive_function_definition apply
    | FunctionApplication -> convert_function_application apply
    | RecordSet -> convert_record_set apply
    | RecordConstructor -> convert_record_constructor apply
    | RecordSelect -> convert_record_select apply
    | Except -> convert_except apply
    | IfThenElse -> convert_if_then_else apply
    | Case -> convert_case apply
    | Subexpression -> convert_subexpression apply
    (* Grouping operators used within other operators *)
    | Pair | Sequence
    (* Proof step operators *)
    | CaseProofStep | PickProofStep | TakeProofStep | HaveProofStep | WitnessProofStep | SufficesProofStep | QedProofStep
      -> conversion_failure ("Operator invalid at this location : " ^ Xml.show_built_in_operator op.operator) apply.node.location

(** Converts a top-level module node. *)
and convert_module_node (mule : Xml.module_node) : Module.T.mule =
  (** Converts an entry, which is an abstract type that can be all sorts of
      things; SANY heavily uses GUIDs to reference one entity from another and
      those GUIDs are resolved in a global table with no real type information.
      Thus in-scope operator parameters coexist alongside entire modules, and
      here we branch out to the appropriate conversion method.
  *)
  let convert_entry (unit : Xml.unit_kind) : Module.T.modunit option =
    match unit with
    | Instance instance -> Some (convert_unit_instance instance)
    | UseOrHide use_or_hide -> Some (convert_use_or_hide use_or_hide)
    | Ref uid -> let entry = resolve_ref mule.node uid in
    match entry.kind with
    | ModuleNode submod -> Some (Submod (convert_module_node submod) |> attach_props submod.node)
    | AssumeNode assume -> Some (convert_assume_node assume)
    | OpDeclNode op_decl_node -> Some (convert_op_decl_node op_decl_node)
    | UserDefinedOpKind user_defined_op_kind -> convert_unit_user_defined_op_kind user_defined_op_kind mule.name
    | TheoremNode theorem_node -> Some (convert_theorem_node entry.uid 0 theorem_node)
    | ModuleInstanceKind instance -> Some (convert_unit_instance instance)
    | BuiltInKind _ -> conversion_failure "BuiltInKind not expected at module top-level" None
    | FormalParamNode _ -> conversion_failure "FormalParamNode not expected at module top-level" None
    | AssumeDefNode assume -> conversion_failure "AssumeDefNode should not be converted directly" None
    | TheoremDefNode theorem_def_node -> conversion_failure "TheoremDefNode should not be converted directly" None
  in {
    name = noprops mule.name;
    extendees = List.map (fun name -> noprops name) mule.extends;
    instancees = []; (* TODO: collate list of instancees from units *)
    body = List.filter_map convert_entry mule.units;
    defdepth = 0;
    stage = Parsed;
    important = false
  } |> attach_props mule.node

(** Converts M(x, y) == INSTANCE ModuleName WITH op <- x, op2 <- y. Also
    converts non-named (anonymous) unit-level instances.

    TODO: SANY can handle named instances accepting an operator as a
    parameter, but TLAPM does not seem to be able to represent this; it uses
    a simple 'hint' for the parameter name instead of a hint * shape tuple
    which would capture arity. This doesn't *necessarily* mean that TLAPM
    does not handle operator parameters, but it is odd that arity info is not
    captured. For now we will just error in that case.
*)
and convert_instance (instance : Xml.instance_node) : Expr.T.instance =
  let mk_arg (param : Xml.formal_param_node) : hint =
    match param.arity with
    | 0 -> attach_props param.node param.name
    | _ -> conversion_failure "TLAPM cannot handle operators as instance arguments" param.node.location
  in let mk_substitution (sub : Xml.substitution) : (hint * Expr.T.expr) =
    let target = resolve_op_decl_node instance.node sub.target_uid in (
      attach_props target.node target.name,
      convert_expression_or_operator_argument instance.node sub.substitute
    )
  in {
    inst_args = instance.parameters |> List.map (resolve_formal_param_node instance.node) |> List.map mk_arg;
    inst_mod = instance.module_name;
    inst_sub = List.map mk_substitution instance.substitutions;
  }

(** INSTANCE conversion at the module unit level. This just wraps a converted
    instance in a Definition or Anoninst variant.
*)
and convert_unit_instance (instance : Xml.instance_node) : Module.T.modunit = (
  let instantiation = convert_instance instance in
  match instance.name with
  | Some name -> Definition (Instance (noprops name, instantiation) |> noprops, User, Hidden, Export)
  | None -> Anoninst (instantiation, if instance.local then Local else Export)
) |> attach_props instance.node

(** Converts USE x, y, z and HIDE a, b, c statements. These statements will
    reveal or conceal the given definitions to all subsequent proof steps.
    The USE ONLY x, y, z statement ensures that only the given definitions
    will be considered in subsequent proof steps.
*)
and convert_use_or_hide (use_or_hide : Xml.use_or_hide_node) : Module.T.modunit =
  let action = if use_or_hide.hide then `Hide else `Use use_or_hide.only in
  Mutate (action, convert_usable use_or_hide) |> attach_props use_or_hide.node

(** Called both from unit-level USE/HIDE conversion and from proof step USE/
    HIDE conversion. De-duplication of shared conversion logic.
*)
and convert_usable (use_or_hide : Xml.use_or_hide_node) : Proof.T.usable = {
  facts = List.map convert_expression use_or_hide.facts;
  defs = List.map (resolve_def use_or_hide.node) use_or_hide.def_refs;
}

(** Converts an ASSUME unit-level construct. This can be named or unnamed. If
    named, this name is given by resolving a reference to an AssumeDefNode,
    which is different from an AssumeNode. Probably this duplication will be
    removed on the SANY side eventually.
*)
and convert_assume_node (assume : Xml.assume_node) : Module.T.modunit =
  Module.T.Axiom (
    Option.map (fun uid -> let def = resolve_assume_def_node assume.node uid in attach_props def.node def.name) assume.definition,
    convert_expression assume.body
  ) |> attach_props assume.node

(** Converts operator declarations such as CONSTANTS and VARIABLES. In a
    declaration like VARIABLES x, y, z, each of x, y, and z are given as
    separate OpDeclNode entries. In contrast, TLAPM wraps all of these in a
    single Variables modunit.
*)
and convert_op_decl_node (xml : Xml.op_decl_node) : Module.T.modunit =
  match xml.kind with
  | Constant -> attach_props xml.node (Constants [attach_props xml.node xml.name, match xml.arity with | 0 -> Shape_expr | n -> Shape_op n])
  | Variable -> attach_props xml.node (Variables [attach_props xml.node xml.name])
  | _ -> todo "Operator declaration kind" (Xml.show_declaration_kind xml.kind) xml.node.location

(** Converts fairness expressions such as WF_sub(expr) and SF_sub(expr).
*)
and convert_fairness (fairness : fairness_op) (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | [], [Expression sub; Expression expr] -> Fair (fairness, convert_expression sub, convert_expression expr)
  | _ -> conversion_failure "Wrong number of operands to fairness expression" apply.node.location
) |> attach_props apply.node

(** Converts action-level expressions such as [expr]_sub and <<expr>>_sub.
    TODO: construct the TSub type if this is prefixed with [] or <>.
*)
and convert_action_expr (op : modal_op) (apply : Xml.op_appl_node) : Expr.T.expr =
  match apply.operands with
  | [Expression expr; Expression sub] -> Sub (
    op,
    convert_expression expr,
    convert_expression sub
  ) |> attach_props apply.node
  | _ -> conversion_failure "Wrong number of operands to action expression" apply.node.location

(** This method handles conversion of four cases:
    1. Bounded non-tuple choice like CHOOSE x \in S : P
    2. Bounded tuple choice like CHOOSE <<x, y>> \in S : P
    3. Unbounded non-tuple choice like CHOOSE x : P
    4. Unbounded tuple choice like CHOOSE <<x, y>> : P

    The XML representation of these does not really adhere very well to the
    principle of making invalid state unrepresentable, so there is a range of
    possible input data that theoretically should never occur but nonetheless
    must be handled in OCaml match statements.
*)
and convert_choose (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  (* Case 1: Bounded non-tuple CHOOSE expression *)
  | [Bound {is_tuple = false; symbol_refs = [param]; expression}], [Expression body] ->
    Choose (
      resolve_bound_symbol apply.node param,
      Some (convert_expression expression),
      convert_expression body
    )
  (* Case 2: Bounded tuple CHOOSE expression *)
  | [Bound ({is_tuple = true} as symbol)], [Expression body] ->
    ChooseTuply (
      List.map (resolve_bound_symbol apply.node) symbol.symbol_refs,
      Some (convert_expression symbol.expression),
      convert_expression body
    )
  (* Case 3: Unbounded non-tuple CHOOSE expression *)
  | [Unbound ({is_tuple = false} as symbol)], [Expression body] ->
    Choose (
      resolve_bound_symbol apply.node symbol.symbol_ref,
      None,
      convert_expression body
    )
  (* Case 4: Unbounded tuple CHOOSE expression; this is the only place in TLA+ where an unbounded tuple quantifier is valid. *)
  | Unbound {is_tuple = true} :: _, [Expression body] ->
    let symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Unbound ({is_tuple = true} as u) -> Some u | _ -> None) apply.bound_symbols in
    if List.length symbols <> List.length apply.bound_symbols
    then conversion_failure "Inconsistent bound/unbound or tuple/non-tuple symbols in CHOOSE" apply.node.location
    else ChooseTuply (
      List.map (fun (s : Xml.unbound_symbol) -> resolve_bound_symbol apply.node s.symbol_ref) symbols,
      None,
      convert_expression body
    )
  | _ -> conversion_failure "Invalid number of bounds or operands to CHOOSE" apply.node.location
) |> attach_props apply.node

(** General utility function to convert the given bound symbol into a non-
    tuple bound type.
*)
and convert_non_tuply_bounds (node : Xml.node) (bound : Xml.bound_symbol) : bounds =
  if bound.is_tuple then conversion_failure "Tuple bound passed to non-tuple bound conversion" node.location else
  match List.map (resolve_bound_symbol node) bound.symbol_refs with
  (* TODO: figure out meaning of "Unknown" parameter *)
  | hd :: tl -> (hd, Unknown, Domain (convert_expression bound.expression))
    :: List.map (fun s -> (s, Unknown, Ditto)) tl
  | [] -> conversion_failure "Bound symbol groups must have at least one symbol" node.location

(** General utility function to convert the given bound symbol into a tuply
    bound type, regardless of whether it is of the form <<x, y>> \in S. If
    even one quantifier bound in a list of quantifier bounds has tuple form,
    then all must be put in the tuply_bounds type; see comment on the
    convert_quantification function for more info.
*)
and convert_tuply_bounds (node : Xml.node) (bound : Xml.bound_symbol) : tuply_bounds =
  if bound.is_tuple
  then match List.map (resolve_bound_symbol node) bound.symbol_refs with
  | (_ :: _ as symbols) -> [(Bound_names symbols, Domain (convert_expression bound.expression))]
  | [] -> conversion_failure "Tuple bound symbol groups must have at least one symbol" node.location
  else match List.map (resolve_bound_symbol node) bound.symbol_refs with
  | hd :: tl -> (Bound_name hd, Domain (convert_expression bound.expression))
    :: List.map (fun s -> (Bound_name s, Ditto)) tl
  | [] -> conversion_failure "Bound symbol groups must have at least one symbol" node.location

(** General utility function to convert a list of quantifier bounds either to
    tuple or non-tuple type. If even one quantifier bound in a list of quantifier
    bounds has tuple form, then all must be put in the tuply_bounds type; see
    comment on the convert_quantification function for more info. This function
    requires all bounds to actually have a set bound, and will error if given
    an unbounded quantifier bound.
*)
and convert_bounds (node : Xml.node) (all_bound_symbols : Xml.symbol list) : bounds_kind =
  let bound_symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Bound b -> Some b | _ -> None) all_bound_symbols in
  if List.length bound_symbols <> List.length all_bound_symbols
  then conversion_failure "Cannot have unbound symbols" node.location
  else if List.exists (fun (b : Xml.bound_symbol) -> b.is_tuple) bound_symbols
  then Tuply (List.map (convert_tuply_bounds node) bound_symbols |> List.flatten)
  else NonTuply (List.map (convert_non_tuply_bounds node) bound_symbols |> List.flatten)

(** General utility function to convert a list of quantifier bounds either to
    tuple or non-tuple type. As above, one tuple bound means all are given as
    tuple bounds. The difference between this and the convert_bounds function
    is that unbounded symbols are accepted here, albeit not unbounded tuple
    bounds (those are only acceptable within a CHOOSE expression). However,
    if one quantifier bound is unbounded, then all must be unbounded.
*)
and convert_bound_or_unbound_symbols (node : Xml.node) (all_symbols : Xml.symbol list) : bounds_kind =
  let bound_symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Bound b -> Some b | _ -> None) all_symbols in
  let unbound_symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Unbound b -> Some b | _ -> None) all_symbols in
  if unbound_symbols <> []
  then
    if bound_symbols <> []
    then conversion_failure "Cannot mix bound and unbound symbols" node.location
    else if List.exists (fun (b : Xml.unbound_symbol) -> b.is_tuple) unbound_symbols
    then conversion_failure "Unbounded tuple quantification is not supported" node.location
    else let mk_bound (bound : Xml.unbound_symbol) : bound = (
      resolve_bound_symbol node bound.symbol_ref,
      Unknown, (* TODO: figure out purpose of this parameter *)
      No_domain
    ) in NonTuply (List.map mk_bound unbound_symbols)
  else if List.exists (fun (b : Xml.bound_symbol) -> b.is_tuple) bound_symbols
  (* Bounded, includes at least one tuple *)
  then Tuply (List.map (convert_tuply_bounds node) bound_symbols |> List.flatten)
  (* Bounded, no tuples *)
  else NonTuply (List.map (convert_non_tuply_bounds node) bound_symbols |> List.flatten)

(** Handles conversion of both bounded & unbounded quantification. Both sides
    of the conversion here are fairly weird. The SANY AST has the same issues
    as in the CHOOSE conversion where many invalid states are representable
    although at least the troublesome unbounded tuple case does not exist.
    The TLAPM AST has an artificial distinction between tuple and non-tuple
    quantification due to support for tuple quantification being added at a
    later date. In reality, mixed tuple/non-tuple quantification is a regular
    feature of TLA+ so ideally these would be folded into a single variant.
    This is perhaps a good target for future refactoring. TLAPM's method of
    representing bounds is also very odd (and that oddity is, unfortunately,
    made worse by its duplication in the tuply_bounds type). Of particular
    note is the bound_domain type, a variant which encompasses an ordinary
    domain expression, no domain, and also "ditto". The latter is used to
    indicate that the domain of a bound is the same as the previous bound's
    domain. At a functional level this is complex to deal with as it means
    each bound must be processed in sequence with knowledge of the previous
    bound's domain, necessitating use of fold instead of map. The resulting
    code never fails to be mind-bending. It also allows representation of
    invalid states, as bound & unbound quantification cannot be mixed in
    valid TLA⁺ syntax. Ideally quantification would be split at the top level
    between bound & unbound, where the bound case has a nonempty list of
    bounds, each of which is either tuple or non-tuple and consists of a
    nonempty list of symbols and a domain expression. The unbound case would
    be a simple nonempty list of symbols.
*)
and convert_quantification (quant : Expr.T.quantifier) (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | _ :: _, [Expression body] -> (
      match convert_bound_or_unbound_symbols apply.node apply.bound_symbols with
      | Tuply tuply_bounds -> QuantTuply (quant, tuply_bounds, convert_expression body)
      | NonTuply bounds -> Quant (quant, bounds, convert_expression body)
    )
  | _ -> conversion_failure "Invalid number of bounds or operands to quantification" apply.node.location
) |> attach_props apply.node

(** Temporal quantification; these symbols are always unbound.
*)
and convert_temporal_quantification (quant : Expr.T.quantifier) (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | _ :: _, [Expression body] ->
    let unbound_symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Unbound b -> Some b | _ -> None) apply.bound_symbols in
    if List.length unbound_symbols <> List.length apply.bound_symbols
    then conversion_failure "Temporal quantification requires unbound symbols" apply.node.location
    else if List.exists (fun (b : Xml.unbound_symbol) -> b.is_tuple) unbound_symbols
    then conversion_failure "Unbounded tuple quantification is not supported" apply.node.location
    else let bounds = List.map (fun (b : Xml.unbound_symbol) -> resolve_bound_symbol apply.node b.symbol_ref) unbound_symbols in
    Tquant (quant, bounds, convert_expression body)
  | _ -> conversion_failure "Invalid number of bounds or operands to temporal quantification" apply.node.location
) |> attach_props apply.node

(** Conversion of expressions of the form {f(x, y) : x \in S, y \in Z}
*)
and convert_set_map (apply : Xml.op_appl_node) : Expr.T.expr =
  match apply.bound_symbols, apply.operands with
  | _ :: _, [Expression body] -> (
      match convert_bounds apply.node apply.bound_symbols with
      | Tuply tuply_bounds -> SetOfTuply (convert_expression body, tuply_bounds)
      | NonTuply bounds -> SetOf (convert_expression body, bounds)
    ) |> attach_props apply.node
  | _ -> conversion_failure "Invalid number of bounds or operands to set mapping" apply.node.location

(** Conversion of expressions of the form {x \in S : P(x)} or {<<x, y>> \in S \X T : P(x, y)}
*)
and convert_set_filter (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | [Bound {symbol_refs = [symbol_ref]; is_tuple = false; expression}], [Expression predicate] -> SetSt (
    resolve_bound_symbol apply.node symbol_ref,
    convert_expression expression,
    convert_expression predicate
  )
  | [Bound {symbol_refs = (_ :: _) as symbol_refs; is_tuple = true; expression}], [Expression predicate] -> SetStTuply (
    List.map (resolve_bound_symbol apply.node) symbol_refs,
    convert_expression expression,
    convert_expression predicate
  )
  | _ -> conversion_failure "Invalid bounds or operands to set filter" apply.node.location
) |> attach_props apply.node

(** Conversion of recursive functions where the function body refers to the
    function definition, for example f[x \in Nat] == f[x - 1]. Both SANY and
    TLAPM represent these as f == [x \in Nat |-> f[x - 1]], and here we
    convert the right-hand side of this definition. The function name is
    introduced as the first symbol, unbound.
*)
and convert_recursive_function_definition (apply : Xml.op_appl_node) : Expr.T.expr = (
  let bounds, body = match apply.bound_symbols, apply.operands with
    | Unbound function_name :: (_ :: _ as all_bound_symbols), [Expression body] ->
      all_bound_symbols, convert_expression body
    | _ -> conversion_failure "Invalid number of bounds or operands to function definition" apply.node.location
  in match convert_bounds apply.node bounds with
  | Tuply tuply_bounds -> FcnTuply (tuply_bounds, body)
  | NonTuply bounds -> Fcn (bounds, body)
) |> attach_props apply.node

(** Converts function construction expressions like [x \in S, y \in P |-> x + y]
    and also f[x \in S, y \in P] == x + y.
*)
and convert_function_constructor (apply : Xml.op_appl_node) : Expr.T.expr =
  match apply.bound_symbols, apply.operands with
  | _ :: _, [Expression body] -> (
      match convert_bounds apply.node apply.bound_symbols with
      | Tuply tuply_bounds -> FcnTuply (tuply_bounds, convert_expression body)
      | NonTuply bounds -> Fcn (bounds, convert_expression body)
    ) |> attach_props apply.node
  | _ -> conversion_failure "Invalid operands to function constructor" apply.node.location

(** Converts function set expressions of the form [P -> Q]
*)
and convert_function_set (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | [], [Expression domain; Expression range] ->
    Arrow (convert_expression domain, convert_expression range)
  | _ -> conversion_failure "Invalid operands to function set expression" apply.node.location
) |> attach_props apply.node

(** Conversion of function application, like f[x, y, z]. Function application
    with multiple arguments is represented using a tuple, with the special
    case of a tuple with a single element being just that tuple itself as an
    argument instead of the argument being destructured from it. The empty
    tuple argument is also a weird one which must be handled. So:
     - f[x] args given as expression x, transformed into list [x]
     - f[x, y] args given as a tuple <<x, y>>, transformed into list [x; y]
     - f[<<x>>] args given as tuple <<x>>, transformed into list [<<x>>]
     - f[<<>>] args given as tuple <<>>, transformed into list [<<>>]

     TODO: validate all of these cases
*)
and convert_function_application (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | [], [Expression fn; Expression args] -> (
      let args = match args with
      | OpApplNode {node; operator; operands} when is_builtin_op apply.node operator TupleLiteral -> (
        match operands with
        | [] -> [args] (* Empty tuple *)
        | [Expression single_arg] -> [args] (* Tuple with single element *)
        | _ -> as_expr_ls __FUNCTION__ node.location operands (* Tuple with multiple elements *)
        )
      | _ -> [args] (* Not a tuple; single expression *)
      in FcnApp (convert_expression fn, List.map convert_expression args)
    )
  | _ -> conversion_failure "Invalid operands to function application" apply.node.location
) |> attach_props apply.node

(** Conversion of record selection expressions like r.fieldName
*)
and convert_record_select (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | [], [Expression record; Expression (StringNode {value})] -> Dot (convert_expression record, value)
  | _ -> conversion_failure "Invalid operands to record selection" apply.node.location
) |> attach_props apply.node

(** Conversion of record set expressions like [field1 : expr1, field2 : expr2, ...]
*)
and convert_record_set (apply : Xml.op_appl_node) : Expr.T.expr =
  convert_record_operator apply (fun arg -> Rect arg)

(** Conversion of record construction expressions like [field1 |-> expr1, field2 |-> expr2, ...]
*)
and convert_record_constructor (apply : Xml.op_appl_node) : Expr.T.expr =
  convert_record_operator apply (fun arg -> Record arg)

(** The conversion logic for both record sets and record constructors is
    identical except for the wrapping constructor (Rect vs Record). This
    method captures that shared logic, taking the constructor as a parameter.
*)
and convert_record_operator (apply : Xml.op_appl_node) (constructor : (string * Expr.T.expr) list -> Expr.T.expr_) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | [], _ :: _ ->
    let mk_field (left, right : Xml.expression * Xml.expression) : (string * Expr.T.expr) =
      match left, right with
      | StringNode {value}, expr -> (value, convert_expression expr)
      | _ -> conversion_failure "Expected field name to be a string" apply.node.location
    in apply.operands |> List.map (as_pair apply.node) |> List.map mk_field |> constructor
  | _ -> conversion_failure "Invalid operands to record operator" apply.node.location
) |> attach_props apply.node

(** Converts expressions of the form [f EXCEPT ![1].2[<<3, 4>>] = val, ![2] = val2, ...]
    Note that SANY does not distinguish between function and record EXCEPT;
    the expression [f EXCEPT !["field"] = val] is the same as [f EXCEPT !.field = val].
    TLAPM *does* distinguish these with the Except_dot and Except_apply variants,
    so we make a best-effort attempt to determine which is which. Whether this
    leads to buggy behavior is currently unknown (TODO).
*)
and convert_except (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | [], Expression base :: (_ :: _ as updates) ->
    let mk_path (path_item : Expr.T.expr) : Expr.T.expoint =
      match path_item.core with
      | String s -> Except_dot s
      | _ -> Except_apply path_item
    in let mk_update (operand : Xml.expr_or_op_arg) : (Expr.T.expoint list * Expr.T.expr) option =
      match operand with
      | Expression OpApplNode {operator; bound_symbols = []; operands = [Expression OpApplNode {operator = update_op; bound_symbols = []; operands = update_path}; Expression new_value]} -> (
        match (resolve_ref apply.node operator).kind, (resolve_ref apply.node update_op).kind with
        | BuiltInKind {operator = Pair}, BuiltInKind {operator = Sequence} ->
          let path = update_path |> as_expr_ls __FUNCTION__ apply.node.location |> List.map convert_expression in
          Some (List.map mk_path path, convert_expression new_value)
        | _ -> None
      ) | _ -> None
    in let updates_converted = List.filter_map mk_update updates in
    if List.length updates_converted <> List.length updates
    then conversion_failure "Invalid operands to EXCEPT; expected pairs of update paths and new values" apply.node.location
    else Except (convert_expression base, updates_converted)
  | _ -> conversion_failure "Invalid operands to EXCEPT" apply.node.location
) |> attach_props apply.node

(** Conversion of expression IF predicate THEN A ELSE B
*)
and convert_if_then_else (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | [], [Expression cond; Expression then_branch; Expression else_branch] ->
    If (convert_expression cond, convert_expression then_branch, convert_expression else_branch)
  | _ -> conversion_failure "Invalid operands to IF/THEN/ELSE" apply.node.location
) |> attach_props apply.node

(** Conversion of expression CASE p1 -> e1 [] p2 -> e2 [] ... [] OTHER -> e.
    Operands are given as a list of (predicate, expression) pairs, with the
    optional final OTHER node having its predicate represented as a string
    with value "$Other"; this will likely be changed on the SANY side in the
    future, as it's equivalent in representation to the plausible syntax
    CASE "$Other" -> expr.
*)
and convert_case (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | [], _ :: _ -> (
      let cases = List.map (as_pair apply.node) apply.operands in
      let mk_case ((predicate, expr) : Xml.expression * Xml.expression) : (Expr.T.expr * Expr.T.expr) =
        (convert_expression predicate, convert_expression expr)
      in match split_last_ls apply.node cases with
      | prefix, (StringNode {value = "$Other"}, other) -> Case (List.map mk_case prefix, Some (convert_expression other))
      | _ -> Case (List.map mk_case cases, None)
    )
  | _ -> conversion_failure "Invalid bound symbols or operands to CASE" apply.node.location
) |> attach_props apply.node

(** Subexpressions like M!N!op(expr)!1.
    TODO: SANY currently does not export all the info needed for this.
*)
and convert_subexpression (apply : Xml.op_appl_node) : Expr.T.expr = (
  raise (Unsupported_language_feature (Option.map convert_location apply.node.location, Subexpression)))

(** SANY gives references like M!op as opaque strings; these are resolved
    using the UID system. We need to parse these back into Bang instances.
    Probably this could most easily be done on the SANY side then attached
    to various references, but we will do it here for now. Note that these
    will not contain subexpression elements like :, <<, @, etc. because those
    would have been given by SANY as the $Nop operator and thus are handled
    in the convert_subexpression method.
    TODO: How are things like M!N(a)!op represented?
*)
and convert_definition_reference (node : Xml.node) (name : string) (op_or_apply : [ `Op | `Apply of Xml.expr_or_op_arg list]) : Expr.T.expr =
  let convert_selector (component : string) : Expr.T.sel =
    if String.contains component '('
    then todo "Definition reference" "Function application in selector" node.location
    else Sel_lab (component, [])
  in let components = String.split_on_char '!' name in
  if List.mem "" components then todo "Definition reference" "!!" node.location
  else match components with
  | [] -> conversion_failure "Unexpected empty definition reference" node.location
  | [component] -> (
    match op_or_apply with
    | `Op -> Opaque name |> attach_props node
    | `Apply args -> Apply (
        Opaque name |> attach_props node,
        List.map (convert_expression_or_operator_argument node) args
      ) |> attach_props node
    )
  | head :: tail ->
    let prefix, last = split_last_ls node tail in
    let last = Sel_lab (
      last,
      List.map (convert_expression_or_operator_argument node) (match op_or_apply with | `Op -> [] | `Apply args -> args)
    ) in Bang (
      Opaque head |> noprops,
      List.map convert_selector prefix @ [last]
    ) |> attach_props node

(** Conversion of application of user-defined operators, including operators
    defined in the standard modules.
*)
and convert_user_defined_op_appl (apply : Xml.op_appl_node) (op : Xml.user_defined_op_kind) : Expr.T.expr =
  convert_definition_reference apply.node op.name (`Apply apply.operands)

(** Conversion of reference to in-scope operator parameters, such as in
    op(a, b, c) == a. This is a case where information is actually lost,
    since the reference is converted to a simple string that will be resolved
    again later on by turning it into a De Bruijn index (Ix) type.
*)
and convert_formal_param_node_op_appl (apply : Xml.op_appl_node) (param : Xml.formal_param_node) : Expr.T.expr =
  match param.arity with
  | 0 -> Opaque param.name |> attach_props param.node
  | n -> Apply (
      Opaque param.name |> attach_props param.node,
      List.map (convert_expression_or_operator_argument apply.node) apply.operands
    ) |> attach_props apply.node

(** Conversion of reference to module-level constants or variables. Again
    information is lost and the string will need to be resolved into a De
    Bruijn index later on.
*)
and convert_op_decl_node_op_appl (apply : Xml.op_appl_node) (decl : Xml.op_decl_node) : Expr.T.expr =
  convert_definition_reference apply.node decl.name (`Apply apply.operands)

(** OpApplNode is a very general node used by SANY to represent essentially
    all expression types. Things like \A x \in S : P are represented as an
    application of the built-in "forall" operator, with operand P and symbol
    x bound by S. This complicated method de-abstracts this into the more
    detailed Expr.T.expr variant type used by TLAPS.
*)
and convert_op_appl_node (apply : Xml.op_appl_node) : Expr.T.expr =
  let op_kind = (resolve_ref apply.node apply.operator).kind in
  match op_kind with
  (* Operators like = and \cup but also CHOOSE and \A *)
  | BuiltInKind op -> convert_built_in_op_appl apply op
  (* An operator defined by the user, including operators in the standard modules *)
  | UserDefinedOpKind userdef -> convert_user_defined_op_appl apply userdef
  (* A reference to an in-scope operator parameter *)
  | FormalParamNode param -> convert_formal_param_node_op_appl apply param
  (* A reference to a CONSTANT or VARIABLE identifier *)
  | OpDeclNode decl -> convert_op_decl_node_op_appl apply decl
  (* A reference to a named THEOREM or a proof step *)
  | TheoremDefNode thm -> convert_definition_reference thm.node thm.name `Op
  (* A reference to a named ASSUME node *)
  | AssumeDefNode assume -> convert_definition_reference assume.node assume.name `Op
  | _ -> conversion_failure ("Invalid operator reference in OpApplNode : " ^ (Xml.show_entry_kind op_kind)) apply.node.location

(** Some places in TLA⁺ syntax allow both normal expressions and also
    operators. Mainly this occurs when applying an operator that could accept
    another operator as a parameter. So any time the user calls an operator
    like op(x, y, z), x, y, and z can each be either expressions or operator
    references. LAMBDA operators can also appear here.
*)
and convert_expression_or_operator_argument (node : Xml.node) (op_expr : Xml.expr_or_op_arg) : Expr.T.expr =
  match op_expr with
  | Expression expr -> convert_expression expr
  | OpArg uid -> match (resolve_ref node uid).kind with
    | FormalParamNode param -> Opaque param.name |> attach_props param.node
    | UserDefinedOpKind userdef ->
      (* The XML export format identifies lambda operators with just the string name LAMBDA *)
      if userdef.name = "LAMBDA" then convert_lambda userdef else
      convert_definition_reference userdef.node userdef.name `Op
    | BuiltInKind builtin ->
      let op = sany_to_tlapm_builtin builtin.node builtin.operator in
      Internal op |> attach_props builtin.node
    | OpDeclNode decl -> convert_definition_reference decl.node decl.name `Op
    | ModuleInstanceKind instance -> conversion_failure ("Invalid operator argument reference to module instance: " ^ Option.get instance.name) instance.node.location
    | AssumeNode assume -> conversion_failure "Invalid operator argument reference to ASSUME" assume.node.location
    | AssumeDefNode assume -> conversion_failure ("Invalid operator argument reference to ASSUME: " ^ assume.name) assume.node.location
    | TheoremNode thm -> conversion_failure "Invalid operator argument reference to THEOREM" thm.node.location
    | TheoremDefNode thm -> conversion_failure ("Invalid operator argument reference to THEOREM: " ^ thm.name) thm.node.location
    | ModuleNode mule -> conversion_failure ("Invalid operator argument reference to MODULE: " ^ mule.name) mule.node.location

(** Converts a basic expression type, which will be either a primitive value
    or an operator application.
*)
and convert_expression (expr : Xml.expression) : Expr.T.expr =
  match expr with
  (* TODO: true means @ from EXCEPT, false means @ from proof step (???) *)
  | AtNode at_node -> At true |> attach_props at_node.node
  | DecimalNode {node; integralPart; fractionalPart} -> Num (Int.to_string integralPart, Int.to_string fractionalPart) |> attach_props node
  | LabelNode label -> convert_label label
  | LetInNode let_in -> convert_let_in_node let_in
  | NumeralNode n -> Num (Int.to_string n.value, "") |> attach_props n.node
  | OpApplNode apply -> convert_op_appl_node apply
  | StringNode s -> String s.value |> attach_props s.node
  | SubstInNode subst -> convert_substitution_in subst
  | TheoremDefRef uid -> todo "Expression" "TheoremDefRef" None
  | AssumeDefRef uid -> todo "Expression" "AssumeDefRef" None

(** Converts LAMBDA x : x + 1 type operators, which can only appear as
    parameters to other operators.
*)
and convert_lambda (op : Xml.user_defined_op_kind) : Expr.T.expr =
  Lambda (
    List.map (convert_leibniz_param_node op.node) op.params,
    convert_expression op.body
  ) |> attach_props op.node

(** When a module has been imported using INSTANCE along with one or more
    substitutions, and then an expression referencing an operator or definition
    from that module is used, that reference is given as a subst_in_node by
    SANY. This provides various details on the substitutions necessary in the
    given expression to properly evaluate it. Here, we throw away all of that
    information and let TLAPM re-derive the substitutions later on in the parse
    process.

    Example:

    M == INSTANCE Mod WITH x <- y
    op == M!op

    Here, the expression M!op is given as a subst_in_node. Compare this with
    an INSTANCE import that does not use substitution:

    M == INSTANCE Naturals
    op == M!Nat

    In this case, M!Nat is actually introduced as a new operator named M!Nat
    in the importing module, and directly referenced with the usual uid-based
    resolution mechanism. This might spell trouble for TLAPM as M!Nat is not
    a valid TLA+ identifier name; TODO check whether this causes trouble.
*)
and convert_substitution_in (subst : Xml.subst_in_node) : Expr.T.expr =
  convert_expression subst.body

(** Converts LET/IN definition sets, consisting of one or more definitions
    followed by a body expression in which the definitions are available.
*)
and convert_let_in_node ({node; def_refs; body} : Xml.let_in_node) : Expr.T.expr =
  let convert_definition (def_ref : int) : Expr.T.defn =
    match (resolve_ref node def_ref).kind with
    | UserDefinedOpKind op -> convert_user_defined_op_kind op
    | _ -> todo "LET/IN definition" "" None
  in Let (List.map convert_definition def_refs, convert_expression body) |> attach_props node

(** Converts user-defined operators defined within LET/IN expressions.
*)
and convert_user_defined_op_kind (op : Xml.user_defined_op_kind) : Expr.T.defn =
  let body = convert_expression op.body in
  (* TLAPS represents op(x) == expr as op == LAMBDA x : expr *)
  let expr = match op.params with
  | [] -> body
  | params ->
    Lambda (List.map (convert_leibniz_param_node op.node) params, body)
    |> attach_props op.node
  in Operator (attach_props op.node op.name, expr) |> attach_props op.node

(** Converts user-defined operators defined in a module top-level. If operator
    was defined in a different module, return None.
*)
and convert_unit_user_defined_op_kind (xml: Xml.user_defined_op_kind) (enclosing_module_name : string) : Module.T.modunit option =
  if (Option.get xml.node.location).filename <> enclosing_module_name then None else
  match xml.recursive with
  | true -> raise (Unsupported_language_feature (Option.map convert_location xml.node.location, RecursiveOperator))
  | false -> Definition (
      convert_user_defined_op_kind xml,
      User,
      Hidden, (* If Visible, will be auto-included in all BY proofs *)
      if xml.local then Local else Export
    ) |> attach_props xml.node |> Option.some

(** This type is redundant with the below TheoremNode type and its conversion
    does not need to be handled. Probably the SANY XML exporter should be
    refactored to combine these two types. The only difference is that this
    type contains the name of the theorem, like in THEOREM thm == expr, while
    the other does not.
*)
and convert_theorem_def_node (theorem_def_node : Xml.theorem_def_node) : Module.T.modunit =
  todo "TheoremDefNode" "" theorem_def_node.node.location

(** Converts theorem nodes. Oddly, SANY has two different theorem node types
    containing identical information except TheoremDefNode contains the name
    and TheoremNode does not. TLAPM's theorem node construction has some
    oddities in the form of additional metadata. The proof is stored twice,
    as one copy is rewritten during proof elaboration while the other remains
    unchanged for error message purposes.
*)
and convert_theorem_node (uid : int) (previous_proof_level : int) (thm : Xml.theorem_node) : Module.T.modunit =
  let proof = convert_proof uid previous_proof_level thm.proof in
  Theorem (
    Option.map (fun uid -> let def = resolve_theorem_def_node thm.node uid in attach_props def.node def.name) thm.definition,
    convert_sequent thm.body,
    0 (* The purpose of this integer parameter is unknown. *),
    proof,
    proof,
    empty_summary
  ) |> attach_props thm.node

(** Converts ASSUME/PROVE constructs; this method de-duplicates some logic
    and is called both from the theorem sequent conversion method and also
    the label conversion method.
*)
and convert_assume_prove (ap : Xml.assume_prove_node) : sequent =
  let convert_hypothesis (hypothesis : Xml.assumption_kind) : Expr.T.hyp =
    match hypothesis with
    | Expression expr -> Fact (convert_expression expr, Visible, NotSet) |> attach_props ap.node
    | NewSymbol ns ->
      let symbol = resolve_op_decl_node ns.node ns.symbol_ref in
      let arity = match symbol.arity with | 0 -> Shape_expr | n -> Shape_op n in
      let kind = match symbol.kind with
        | NewConstant -> Constant
        | NewVariable -> State
        | NewState -> State
        | NewAction -> Action
        | NewTemporal -> Temporal
        | _ -> conversion_failure "Invalid symbol kind in NEW" ns.node.location
      in let domain = match ns.domain with
      | Some domain -> Bounded (convert_expression domain, Hidden)
      | None -> Unbounded
      in Fresh (noprops symbol.name, arity, kind, domain)
      |> attach_props ns.node
    | AssumeProveLike AssumeProveNode apl ->
      Fact (Sequent (convert_assume_prove apl) |> attach_props apl.node, Visible, NotSet) |> attach_props apl.node
    | AssumeProveLike AssumeProveSubstitution apl -> todo "ASSUME/PROVE" "nested ASSUME/PROVE with substitution" apl.node.location
  in {
    context = List.map convert_hypothesis ap.assumptions |> Deque.of_list;
    active = convert_expression ap.prove;
  }

(** Sequents are theorem bodies, which are either simple expressions or
    ASSUME/PROVE constructs.
    TODO: handle ASSUME/PROVE substitution case (uncertain what this is).
*)
and convert_sequent (seq : Xml.expr_or_assume_prove) : sequent =
  match seq with
  | Expression expr -> {context = Deque.empty; active = convert_expression expr}
  | AssumeProveLike AssumeProveNode ap -> convert_assume_prove ap
  | AssumeProveLike AssumeProveSubstitution aps -> todo "Sequent" "ASSUME/PROVE with substitution" aps.node.location

(** Converts lbl(a, b, c) :: expr and lbl(a, b, c) :: ASSUME ... PROVE. TLAPM
    treats labels as parentheses subtypes.
    TODO: Determine whether labels should be able to handle operators here.
*)
and convert_label (label : Xml.label_node) : Expr.T.expr = (
  let mk_arg (param : Xml.formal_param_node) : hint =
    match param.arity with
    | 0 -> attach_props param.node param.name
    | _ -> conversion_failure "TLAPM cannot handle operators as label arguments" param.node.location
  in let parameters = List.map (resolve_formal_param_node label.node) label.parameters |> List.map mk_arg in
  let lbl = Nlabel (label.name, parameters) |> attach_props label.node in
  match label.body with
  | Expression expr -> Parens (convert_expression expr, lbl)
  | AssumeProveLike AssumeProveNode ap -> Parens (Sequent (convert_assume_prove ap) |> attach_props ap.node, lbl)
  | AssumeProveLike AssumeProveSubstitution aps -> todo "Label" "ASSUME/PROVE with substitution" aps.node.location
) |> attach_props label.node

(** Converts a proof, which can either be OMITTED, OBVIOUS, BY, or a series
    of individual proof steps culminated in a QED step. We need to attach a
    proof name to each proof step type, which in most of them is fairly
    meaningless but is required by subsequent TLAPM processing. Thus we just
    attach the incremented previous proof level and the reference UID.
*)
and convert_proof (uid : int) (previous_proof_level : int) (proof : Xml.proof_node_group option) : Proof.T.proof =
  let proof_name = Unnamed (previous_proof_level + 1, uid) in
  match proof with
  | None -> Omitted Implicit |> noprops |> attach_proof_step_name proof_name
  | Some Omitted node -> Omitted Explicit |> attach_props node |> attach_proof_step_name proof_name
  | Some Obvious node -> Obvious |> attach_props node |> attach_proof_step_name proof_name
  | Some By proof -> convert_by_proof proof |> attach_proof_step_name proof_name
  | Some Steps proof -> convert_proof_steps uid proof

(** Converts proofs of the form BY x, y, z DEF a, b, c. This is another place
    where information is lost, as the facts and definitions are converted to
    strings that will need to be resolved to De Bruijn indices later on.
*)
and convert_by_proof ({node; facts; defs; only} : Xml.by_proof_node) : Proof.T.proof =
  By ({
    facts = List.map convert_expression facts;
    defs = List.map (resolve_def node) defs;
  },
  only
) |> attach_props node

(** Extracts the proof step name from a string like <1>abc. This is done by
    taking the substring between the > and either the end of the string or
    the first '.' character. Probably this information should be exposed by
    SANY.
*)
and convert_proof_step_name (node : Xml.node) (uid : int) (proof_level : int) (theorem_def_ref : int option) : stepno =
  match theorem_def_ref with
  | Some uid ->
    let proof_name = (resolve_theorem_def_node node uid).name in
    let name_start = String.index proof_name '>' in
    let name_end = match String.index_opt proof_name '.' with | Some n -> n | None -> String.length proof_name in
    let name_len = name_end - name_start in
    let name = String.sub proof_name name_start name_len in
    Named (proof_level, name, false)
  | None -> Unnamed (proof_level, uid)

(** One possible proof form is a series of steps, culminating in a QED step.
    This method converts that structure.
*)
and convert_proof_steps (uid : int) ({node; proof_level; steps} : Xml.steps_proof_node) : Proof.T.proof =
  let convert_qed_step (qed_proof_step : Xml.proof_step_group) : Proof.T.qed_step =
    match qed_proof_step with
    | TheoremNodeRef uid ->
      let thm = resolve_theorem_node node uid in
      let step_name = convert_proof_step_name node uid proof_level thm.definition in
      Qed (convert_proof uid (step_number step_name) thm.proof) |> attach_props thm.node
      |> attach_proof_step_name step_name
    | _ -> conversion_failure "QED step must be a theorem node" node.location
  in let steps, qed = split_last_ls node steps
  in Steps (
    List.map (convert_proof_step node proof_level) steps,
    convert_qed_step qed
  ) |> attach_props node |> attach_proof_step_name (Unnamed (proof_level, uid))

(** Converts a specific proof step into the Proof.T.step variant expected by
    TLAPM. While TLAPM has thirteen proof variants as of this writing, SANY
    bundles everything into only five: DefStepNode (where the user introduces
    new operator definitions into scope), UseOrHideNode, InstanceNode (removed
    from TLA+; see https://github.com/tlaplus/rfcs/issues/18), TheoremNodeRef,
    and TheoremNode. In keeping with the odd duplication of purpose between
    TheoremDefNode and TheoremNode, the TheoremNode type is not believed to be
    used. TheoremNodeRef is the real workhorse proof step type, as it is used
    for all proof step types that can have sub-proofs. The specific proof step
    subtype is identified by a special built-in operator as the theorem body.
*)
and convert_proof_step (node : Xml.node) (proof_level : int) (step : Xml.proof_step_group) : Proof.T.step =
  match step with
  | InstanceNode {node} -> raise (Unsupported_language_feature (Option.map convert_location node.location, InstanceProofStep))
  | TheoremNode -> todo "TheoremNode proof step" "" None
  | DefStep {node; def_refs} -> convert_definition_proof_step node def_refs
  (* TODO: attach name to UseOrHide step *)
  | UseOrHide use_or_hide -> Use (convert_usable use_or_hide, use_or_hide.only) |> attach_props use_or_hide.node
  | TheoremNodeRef uid ->
    let thm = resolve_theorem_node node uid in
    let step_name = convert_proof_step_name node uid proof_level thm.definition in
    let proof = convert_proof uid (step_number step_name) thm.proof in
    let step = match thm.body with
    | Expression OpApplNode ({operator} as apply) when is_builtin_op node operator CaseProofStep ->
      convert_case_proof_step apply proof
    | Expression OpApplNode ({operator} as apply) when is_builtin_op node operator PickProofStep ->
      convert_pick_proof_step apply proof
    | Expression OpApplNode ({operator} as apply) when is_builtin_op node operator TakeProofStep ->
      convert_take_proof_step apply
    | Expression OpApplNode ({operator} as apply) when is_builtin_op node operator HaveProofStep ->
      convert_have_proof_step apply
    | Expression OpApplNode ({operator} as apply) when is_builtin_op node operator WitnessProofStep ->
      convert_witness_proof_step apply
    | Expression OpApplNode ({operator} as apply) when is_builtin_op node operator SufficesProofStep ->
      convert_suffices_proof_step apply proof
    | _ -> Suffices (convert_sequent thm.body, proof)
    in step |> attach_props thm.node |> attach_proof_step_name step_name

(** Converts DEFINE proof steps, like
      DEFINE
        P(x) == x
        Q(y) == y
        M(z) == INSTANCE Naturals

    TODO: attach name to DefStep step
*)
and convert_definition_proof_step (node : Xml.node) (def_refs : int list) : Proof.T.step =
  let mk_def (uid : int) : Expr.T.defn =
    match (resolve_ref node uid).kind with
    | UserDefinedOpKind op -> convert_user_defined_op_kind op
    | ModuleInstanceKind m -> (
      match m.name with
      | Some name -> Instance (noprops name, convert_instance m) |> attach_props m.node
      | None -> conversion_failure "Unnamed module instance in DEFINE proof step" m.node.location
    )
    | _ -> conversion_failure "Invalid reference type in DEFINE proof step" node.location
  in Define (List.map mk_def def_refs) |> attach_props node

(** Converts CASE proof steps, like: <2>7. CASE UNCHANGED vars
*)
and convert_case_proof_step (apply : Xml.op_appl_node) (proof : Proof.T.proof) : Proof.T.step_ =
  match apply.bound_symbols, apply.operands with
  | [], [Expression expr] -> Pcase (convert_expression expr, proof)
  | _ -> conversion_failure "Invalid operands to CASE proof step" apply.node.location

(** Converts PICK proofs steps, like PICK a, b, c : P
*)
and convert_pick_proof_step (apply : Xml.op_appl_node) (proof : Proof.T.proof) : Proof.T.step_ =
  match apply.bound_symbols, apply.operands with
  | _ :: _, [Expression body] -> (
      match convert_bound_or_unbound_symbols apply.node apply.bound_symbols with
      | Tuply tuply_bounds -> PickTuply (tuply_bounds, convert_expression body, proof)
      | NonTuply bounds -> Pick (bounds, convert_expression body, proof)
    )
  | _ -> conversion_failure "Invalid number of bounds or operands to PICK proof step" apply.node.location

(** Converts TAKE a, b, c, d or TAKE a, b \in S, c \in P, <<d, e>> \in Q
    proof step type.
*)
and convert_take_proof_step (apply : Xml.op_appl_node) : Proof.T.step_ =
  match apply.bound_symbols, apply.operands with
  | _ :: _, [] -> (
      match convert_bound_or_unbound_symbols apply.node apply.bound_symbols with
      | Tuply tuply_bounds -> TakeTuply tuply_bounds
      | NonTuply bounds -> Take bounds
    )
  | _ -> conversion_failure "Invalid number of bounds or operands to TAKE proof step" apply.node.location

(** Converts HAVE P proof steps.
*)
and convert_have_proof_step (apply : Xml.op_appl_node) : Proof.T.step_ =
  match apply.bound_symbols, apply.operands with
  | [], [Expression expr] -> Have (convert_expression expr)
  | _ -> conversion_failure "Invalid bounds or operands to HAVE proof step" apply.node.location

(** Converts WITNESS x, y, z proof steps.
*)
and convert_witness_proof_step (apply : Xml.op_appl_node) : Proof.T.step_ =
  match apply.bound_symbols, apply.operands with
  | [], expressions ->
      Witness (expressions |> as_expr_ls __FUNCTION__ apply.node.location |> List.map convert_expression)
  | _ -> conversion_failure "Invalid bounds or operands to WITNESS proof step" apply.node.location

(** Converts SUFFICES P PROOF BY x, y, z proof steps.
*)
and convert_suffices_proof_step (apply : Xml.op_appl_node) (proof : Proof.T.proof) : Proof.T.step_ =
  match apply.bound_symbols, apply.operands with
  | [], [Expression expr] -> Suffices (convert_sequent (Expression expr), proof)
  | _ -> conversion_failure "Invalid bounds or operands to SUFFICES proof step" apply.node.location

(** The top-level method converting the entire SANY AST to TLAPM's AST. SANY
    uses a lot of GUIDs for one entity to reference another, so we load those
    into a global table for fast lookup. This table would have to be a
    parameter to every conversion method in this file; for simplicity we make
    it a module-level mutable variable instead. This method returns both the
    converted root module and a context, which is a mapping from module names
    to module structures for the transitive closure of modules imported from
    root.
*)
let convert_ast (ast : Xml.modules) : (Module.T.modctx * Module.T.mule, (string option * string)) result =
  entries :=
    List.fold_left
      (fun m (e : Xml.entry) -> Coll.Im.add e.uid e.kind m)
      Coll.Im.empty
      ast.context;
  let ctx : Module.T.modctx = List.fold_left
    (fun (map : Module.T.modctx) (mule_ref : int) ->
      let toplevel_node : Xml.node = {location = None; level = None} in
      let mule : Xml.module_node = resolve_module_node toplevel_node mule_ref in
      match Coll.Sm.find_opt mule.name Module.Standard.initctx with
      | Some std_mule ->
        print_endline ("Using built-in standard module " ^ mule.name);
        Coll.Sm.add mule.name std_mule map
      | None ->
        print_endline ("Converting parsed module " ^ mule.name);
        Coll.Sm.add mule.name (convert_module_node mule) map
    )
    Coll.Sm.empty
    ast.module_refs
  in let root_module = Coll.Sm.find ast.root_module ctx in
  root_module.core.important <- true;
  Ok (ctx, root_module)

(** Calls SANY to parse the given module, then converts SANY's AST into the
    TLAPM AST format.
*)
let parse (module_path : string) : (Module.T.modctx * Module.T.mule, (string option * string)) result =
  let ( >>= ) = Result.bind in
  Option.to_result ~none:(None, "TLAPS standard library cannot be found") Params.stdlib_path
  >>= (Xml.get_module_ast_xml module_path)
  >>= convert_ast
