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

let todo (category : string) (msg : string) (loc : Xml.location option) : 'a =
  let loc = match loc with
  | Some loc -> Xml.show_location loc
  | None -> "Unknown location"
  in failwith (Printf.sprintf "%s not yet implemented: %s\n%s" category msg loc)

let conversion_failure (msg : string) (loc : Xml.location option) : 'a =
  let loc = match loc with
  | Some loc -> Xml.show_location loc
  | None -> "Unknown location"
  in failwith (Printf.sprintf "Conversion failure:\n%s\n%s" msg loc)

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

type proof_level =
 | Previous of int
 | Known of int

(** Parses proof step names like <1>a as given in SANY's XML output, where
    they are escaped using &lt; and &rt; for < and > respectively. Proof step
    name can also be <+>, meaning one more than the previous proof level, or
    <*>, meaning same as the current proof level.
*)
let parse_proof_step_name (proof_level : proof_level) (uid : int) (proof_name : string) : stepno =
  let parse_name (parse_state, level, name : int * char list * char list ) (c : char) : int * char list * char list =
    match parse_state, c with
    (* Start state: expect < or &lt; *)
    | 0, '<' -> (4, level, name)
    | 0, '&' -> (1, level, name)
    | 1, 'l' -> (2, level, name)
    | 2, 't' -> (3, level, name)
    | 3, ';' -> (4, level, name)
    (* Level parsing state: expect '+', '*', or digit *)
    | 4, '+' | 4, '*' -> (6, [c], name)
    (* Parse at least one digit then consume another digit, >, or &rt; *)
    | 4, '0' .. '9' | 5, '0' .. '9' -> (5, c :: level, name)
    | 5, '>' -> (10, level, name)
    | 5, '&' -> (7, level, name)
    (* Have seen + or *, expect > or &rt; *)
    | 6, '>' -> (10, level, name)
    | 6, '&' -> (7, level, name)
    | 7, 'r' -> (8, level, name)
    | 8, 't' -> (9, level, name)
    | 9, ';' -> (10, level, name)
    (* Proof name parsing state: read in zero or more a-zA-Z0-9_ *)
    | 10, 'a' .. 'z' | 10, 'A' .. 'Z' | 10, '0' .. '9' | 10, '_' -> (10, level, c :: name)
    (* Terminating '.' state; consume & ignore *)
    | 10, '.' | 11, '.' -> (11, level, name)
    | _ -> conversion_failure (Format.sprintf "Invalid character '%c' in proof step name '%s' at parsing state %d" c proof_name parse_state) None
  in let (_, level, name) = String.fold_left parse_name (0, [], []) proof_name
  in let digits_to_int (digits : char list) : int =
    List.fold_right (fun (d : char) (acc : int) : int -> (int_of_char d - int_of_char '0') + acc * 10) digits 0
  in let level = match level, proof_level with
  | ['+'], Previous n -> n + 1
  | ['+'], Known _ -> conversion_failure "Cannot have explicit proof level followed by <+>" None
  | ['*'], Previous n -> n + 1
  | ['*'], Known n -> n
  | digits, Previous _ -> digits_to_int digits
  | digits, Known n ->
    let level = digits_to_int digits in
    if level <> n then conversion_failure ("Mismatched proof level: expected " ^ string_of_int n ^ " but got " ^ string_of_int level) None
    else level
  in if name = [] then Unnamed (level, uid) else
  Named (level, name |> List.rev |> List.to_seq |> String.of_seq, false)

(** Wraps the given proof step with its name in the metadata.
*)
let attach_proof_step_name (proof_name : stepno) (step : 'a) : 'a =
  assign step Props.step proof_name

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

(** Wrap the given object in location data.
    TODO: also wrap with level data.
*)
let attach_props (props : Xml.node) (value : 'a) : 'a wrapped =
  match props.location with
  | Some loc -> Util.locate value (convert_location loc)
  | None -> noprops value

(** Look up the given ref in the global entries table, failing if not found.
*)
let resolve_ref (uid : int) : Xml.entry =
  match Coll.Im.find_opt uid !entries with
  | Some kind -> {uid; kind}
  | None -> conversion_failure ("Unresolved reference to entry UID: " ^ string_of_int uid) None

(** A typed version of resolve_ref for module nodes.
*)
let resolve_module_node (uid : int) : Xml.module_node =
  match (resolve_ref uid).kind with
  | ModuleNode mule -> mule
  | _ -> conversion_failure ("Expected module node for UID: " ^ string_of_int uid) None

(** A typed version of resolve_ref for operator declaration nodes.
*)
let resolve_op_decl_node (uid : int) : Xml.op_decl_node =
  match (resolve_ref uid).kind with
  | OpDeclNode odn -> odn
  | _ -> conversion_failure ("Expected operator declaration node for UID: " ^ string_of_int uid) None

(** A typed version of resolve_ref for user-defined operators.
*)
let resolve_user_defined_op_kind (uid : int) : Xml.user_defined_op_kind =
  match (resolve_ref uid).kind with
  | UserDefinedOpKind udok -> udok
  | _ -> conversion_failure ("Expected user defined operator for UID: " ^ string_of_int uid) None

(** A typed version of resolve_ref for operator parameter nodes.
*)
let resolve_formal_param_node (uid : int) : Xml.formal_param_node =
  match (resolve_ref uid).kind with
  | Xml.FormalParamNode xml -> xml
  | _ -> conversion_failure ("Expected formal parameter node for UID: " ^ string_of_int uid) None

(** A typed version of resolve_ref for Leibniz operator parameter nodes.
*)
let resolve_leibniz_formal_param_node (param : Xml.leibniz_param) : (hint * shape) =
  let fpn = resolve_formal_param_node param.ref in (
    attach_props fpn.node fpn.name,
    match fpn.arity with
    | 0 -> Shape_expr
    | n -> Shape_op n
  )

(** A typed version of resolve_ref for theorem definition nodes.
*)
let resolve_theorem_def_node (uid : int) : Xml.theorem_def_node =
  match (resolve_ref uid).kind with
  | TheoremDefNode xml -> xml
  | _ -> conversion_failure ("Expected theorem definition node for UID: " ^ string_of_int uid) None

(** A typed version of resolve_ref for assume definition nodes.
*)
let resolve_assume_def_node (uid : int) : Xml.assume_def_node =
  match (resolve_ref uid).kind with
  | AssumeDefNode xml -> xml
  | _ -> conversion_failure ("Expected assume definition node for UID: " ^ string_of_int uid) None

(** A typed version of resolve_ref for theorem nodes.
*)
let resolve_theorem_node (uid : int) : Xml.theorem_node =
  match (resolve_ref uid).kind with
  | TheoremNode xml -> xml
  | _ -> conversion_failure ("Expected theorem node for UID: " ^ string_of_int uid) None

(** A typed version of resolve_ref for bound symbols.
*)
let resolve_bound_symbol (uid : int) : hint =
  match Coll.Im.find_opt uid !entries with
  | Some (Xml.FormalParamNode ({arity = 0} as xml)) -> attach_props xml.node xml.name
  | Some (Xml.FormalParamNode _) -> conversion_failure ("Bound symbol cannot be an operator: " ^ string_of_int uid) None
  | _ -> conversion_failure ("Unresolved formal parameter node UID: " ^ string_of_int uid) None

(** Resolves definitions referenced in BY proofs or USE/HIDE statements.
*)
let resolve_def (node : Xml.node) (ref : int) : use_def wrapped =
    match (resolve_ref ref).kind with
    | UserDefinedOpKind op -> Dvar op.name |> attach_props op.node
    | TheoremDefNode thm -> Dvar thm.name |> attach_props thm.node
    | other -> conversion_failure ("Invalid definition reference in BY proof: " ^ (Xml.show_entry_kind other)) node.location

let convert_proof_step_name (uid : int) (proof_level : proof_level) (theorem_def_ref : int option) : stepno =
  match theorem_def_ref with
  | Some uid -> parse_proof_step_name proof_level uid (resolve_theorem_def_node uid).name
  | None -> match proof_level with
    | Previous n -> Unnamed (n + 1, uid)
    | Known n -> Unnamed (n, uid)

(** Converts built-in prefix, infix, and postfix operators along with keywords.
*)
let try_convert_builtin (builtin : Xml.built_in_kind) : Builtin.builtin option =
  match builtin.name with
  | "TRUE" -> Some Builtin.TRUE
  | "FALSE" -> Some Builtin.FALSE
  | "STRING" -> Some Builtin.STRING
  | "DOMAIN" -> Some Builtin.DOMAIN
  | "SUBSET" -> Some Builtin.SUBSET
  | "UNCHANGED" -> Some Builtin.UNCHANGED
  | "UNION" -> Some Builtin.UNION
  | "\\lnot" -> Some Builtin.Neg
  | "'" -> Some Builtin.Prime
  | "[]" -> Some (Builtin.Box false)
  | "<>" -> Some Builtin.Diamond
  | "=" -> Some Builtin.Eq
  | "/=" -> Some Builtin.Neq
  | "\\in" -> Some Builtin.Mem
  | "\\notin" -> Some Builtin.Notmem
  | "\\" -> Some Builtin.Setminus
  | "\\union" -> Some Builtin.Cup
  | "\\intersect" -> Some Builtin.Cap
  | "\\subseteq" -> Some Builtin.Subseteq
  | "\\land" -> Some Builtin.Conj
  | "\\lor" -> Some Builtin.Disj
  | "=>" -> Some Builtin.Implies
  | "\\equiv" -> Some Builtin.Equiv
  | _ -> None

(** Conversion of application of all traditional built-in operators like = or
    \cup but also things like CHOOSE and \A which one would ordinarily not
    view as built-in operators.
*)
let rec convert_built_in_op_appl (apply : Xml.op_appl_node) (op : Xml.built_in_kind) : Expr.T.expr =
  match try_convert_builtin op with
  (* Traditional built-in operators *)
  | Some builtin -> Apply (
      Internal builtin |> attach_props op.node,
      apply.operands |> as_expr_ls (Builtin.builtin_to_string builtin) apply.node.location |> List.map convert_expression
    ) |> attach_props apply.node
  (* More abstract kinds of built-in operators *)
  | None ->
    match op.name with
    | "$SetEnumerate" -> SetEnum (
      apply.operands |> as_expr_ls "$SetEnumerate" apply.node.location |> List.map convert_expression
    ) |> attach_props apply.node
    | "$Tuple" -> Tuple (
      apply.operands |> as_expr_ls "$Tuple" apply.node.location |> List.map convert_expression
    ) |> attach_props apply.node
    | "$ConjList" -> List (
      And, apply.operands |> as_expr_ls "$ConjList" apply.node.location |> List.map convert_expression
    ) |> attach_props apply.node
    | "$DisjList" -> List (
      Or, apply.operands |> as_expr_ls "$DisjList" apply.node.location |> List.map convert_expression
    ) |> attach_props apply.node
    | "$CartesianProd" -> Product (
      apply.operands |> as_expr_ls "$CartesianProd" apply.node.location |> List.map convert_expression
    ) |> attach_props apply.node
    | "$WF" -> convert_fairness Weak apply
    | "$BoundedChoose" -> convert_choose apply
    | "$UnboundedChoose" -> convert_choose apply
    | "$SquareAct" -> convert_action_expr Box apply
    | "$BoundedExists" -> convert_quantification Exists apply
    | "$BoundedForall" -> convert_quantification Forall apply
    | "$UnboundedExists" -> convert_quantification Exists apply
    | "$UnboundedForall" -> convert_quantification Forall apply
    | "$SetOfAll" -> convert_set_map apply
    | "$SubsetOf" -> convert_set_filter apply
    | "$SetOfFcns" -> convert_function_set apply
    | "$FcnConstructor" -> convert_function_constructor apply
    | "$RecursiveFcnSpec" -> convert_recursive_function apply
    | "$FcnApply" -> convert_function_application apply
    | "$SetOfRcds" -> convert_record_set apply
    | "$RcdConstructor" -> convert_record_constructor apply
    | "$RcdSelect" -> convert_record_select apply
    | "$Except" -> convert_except apply
    | "$IfThenElse" -> convert_if_then_else apply
    | "$Case" -> convert_case apply
    | s -> todo "Built-in operator" s apply.node.location

(** Converts a top-level module node. *)
and convert_module_node (mule : Xml.module_node) : Module.T.mule =
  (** Converts an entry, which is an abstract type that can be all sorts of
      things; SANY heavily uses GUIDs to reference one entity from another and
      those GUIDs are resolved in a global table with no real type information.
      Thus in-scope operator parameters coexist alongside entire modules, and
      here we branch out to the appropriate conversion method.
  *)
  let convert_entry (unit : Xml.unit_kind) : Module.T.modunit =
    match unit with
    | Instance instance -> convert_instance instance
    | UseOrHide use_or_hide -> convert_use_or_hide use_or_hide
    | Ref uid -> let entry = resolve_ref uid in
    match entry.kind with
    | ModuleNode submod -> Submod (convert_module_node submod) |> attach_props submod.node
    | AssumeNode assume -> convert_assume_node assume
    | OpDeclNode op_decl_node -> convert_op_decl_node op_decl_node
    | UserDefinedOpKind user_defined_op_kind -> convert_unit_user_defined_op_kind user_defined_op_kind
    | TheoremNode theorem_node -> convert_theorem_node entry.uid 0 theorem_node
    | BuiltInKind _ -> conversion_failure "BuiltInKind not expected at module top-level" None
    | FormalParamNode _ -> conversion_failure "FormalParamNode not expected at module top-level" None
    | AssumeDefNode assume -> conversion_failure "AssumeDefNode should not be converted directly" None
    | TheoremDefNode theorem_def_node -> conversion_failure "TheoremDefNode should not be converted directly" None
  in {
    name = noprops mule.name;
    extendees = []; (* TODO: figure out how to get list of modules imported by this module *)
    instancees = [];
    body = List.map convert_entry mule.units;
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
and convert_instance (instance : Xml.instance_node) : Module.T.modunit = (
  let mk_arg (param : Xml.formal_param_node) : hint =
    match param.arity with
    | 0 -> attach_props param.node param.name
    | _ -> conversion_failure "TLAPM cannot handle operators as instance arguments" param.node.location
  in let mk_substitution (sub : Xml.substitution) : (hint * Expr.T.expr) =
    let target = resolve_op_decl_node sub.target_uid in (
      attach_props target.node target.name,
      convert_expression_or_operator_argument sub.substitute
    )
  in let instantiation : Expr.T.instance = {
    inst_args = instance.parameters |> List.map resolve_formal_param_node |> List.map mk_arg;
    inst_mod = instance.module_name;
    inst_sub = List.map mk_substitution instance.substitutions;
  } in match instance.name with
  | Some name -> Definition (Instance (noprops name, instantiation) |> noprops, User, Hidden, Export)
  | None -> Anoninst (instantiation, Export)
) |> attach_props instance.node

and convert_usable (use_or_hide : Xml.use_or_hide_node) : Proof.T.usable = {
  facts = List.map convert_expression use_or_hide.facts;
  defs = List.map (resolve_def use_or_hide.node) use_or_hide.def_refs;
}

and convert_use_or_hide (use_or_hide : Xml.use_or_hide_node) : Module.T.modunit =
  (* TODO: confirm `Use boolean parameter really is the ONLY keyword *)
  let action = if use_or_hide.hide then `Hide else `Use use_or_hide.only in
  Mutate (action, convert_usable use_or_hide) |> attach_props use_or_hide.node

and convert_assume_node (assume : Xml.assume_node) : Module.T.modunit =
  Module.T.Axiom (
    Option.map (fun uid -> let def = resolve_assume_def_node uid in attach_props def.node def.name) assume.definition,
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

(** Converts action-level expressions such as [][expr]_sub and <><<expr>>_sub.
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
      resolve_bound_symbol param,
      Some (convert_expression expression),
      convert_expression body
    )
  (* Case 2: Bounded tuple CHOOSE expression *)
  | [Bound ({is_tuple = true} as symbol)], [Expression body] ->
    ChooseTuply (
      List.map resolve_bound_symbol symbol.symbol_refs,
      Some (convert_expression symbol.expression),
      convert_expression body
    )
  (* Case 3: Unbounded non-tuple CHOOSE expression *)
  | [Unbound ({is_tuple = false} as symbol)], [Expression body] ->
    Choose (
      resolve_bound_symbol symbol.symbol_ref,
      None,
      convert_expression body
    )
  (* Case 4: Unbounded tuple CHOOSE expression *)
  | Unbound {is_tuple = true} :: _, [Expression body] ->
    let symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Unbound ({is_tuple = true} as u) -> Some u | _ -> None) apply.bound_symbols in
    if List.length symbols <> List.length apply.bound_symbols
    then conversion_failure "Inconsistent bound/unbound or tuple/non-tuple symbols in CHOOSE" apply.node.location
    else ChooseTuply (
      List.map (fun (s : Xml.unbound_symbol) -> resolve_bound_symbol s.symbol_ref) symbols,
      None,
      convert_expression body
    )
  | _ -> conversion_failure "Invalid number of bounds or operands to CHOOSE" apply.node.location
) |> attach_props apply.node

and convert_tuply_bounds (node : Xml.node) (bound : Xml.bound_symbol) : tuply_bounds =
  if bound.is_tuple
  then match List.map resolve_bound_symbol bound.symbol_refs with
  | (_ :: _ as symbols) -> [(Bound_names symbols, Domain (convert_expression bound.expression))]
  | [] -> conversion_failure "Tuple bound symbol groups must have at least one symbol" node.location
  else match List.map resolve_bound_symbol bound.symbol_refs with
  | hd :: tl -> (Bound_name hd, Domain (convert_expression bound.expression))
    :: List.map (fun s -> (Bound_name s, Ditto)) tl
  | [] -> conversion_failure "Bound symbol groups must have at least one symbol" node.location

and convert_non_tuply_bounds (node : Xml.node) (bound : Xml.bound_symbol) : bounds =
  match List.map resolve_bound_symbol bound.symbol_refs with
  | hd :: tl -> (hd, Unknown, Domain (convert_expression bound.expression))
    :: List.map (fun s -> (s, Unknown, Ditto)) tl
  | [] -> conversion_failure "Bound symbol groups must have at least one symbol" node.location

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
  | _ :: _, [Expression body] ->
    let bound_symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Bound b -> Some b | _ -> None) apply.bound_symbols in
    let unbound_symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Unbound b -> Some b | _ -> None) apply.bound_symbols in
    if unbound_symbols <> []
    then
      if bound_symbols <> []
      then conversion_failure "Cannot mix bound and unbound symbols in quantification" apply.node.location
      else if List.exists (fun (b : Xml.unbound_symbol) -> b.is_tuple) unbound_symbols
      then conversion_failure "Unbounded tuple quantification is not supported" apply.node.location
      (* Unbounded quantification *)
      else let mk_bound (bound : Xml.unbound_symbol) : bound = (
        resolve_bound_symbol bound.symbol_ref,
        Unknown, (* TODO: figure out purpose of this parameter *)
        No_domain
      ) in Quant (
        quant,
        List.map mk_bound unbound_symbols,
        convert_expression body
      )
    else if List.exists (fun (b : Xml.bound_symbol) -> b.is_tuple) bound_symbols
    (* Bounded quantification that includes at least one tuple *)
    then QuantTuply (
      quant,
      List.map (convert_tuply_bounds apply.node) bound_symbols |> List.flatten,
      convert_expression body
    )
    (* Bounded quantification without any tuples *)
    else Quant (
      quant,
      List.map (convert_non_tuply_bounds apply.node) bound_symbols |> List.flatten,
      convert_expression body
    )
  | _ -> conversion_failure "Invalid number of bounds or operands to quantification" apply.node.location
) |> attach_props apply.node

(** Conversion of expressions of the form {f(x, y) : x \in S, y \in Z}
*)
and convert_set_map (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | _ :: _, [Expression body] ->
    let bound_symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Bound b -> Some b | _ -> None) apply.bound_symbols in
    if List.length bound_symbols <> List.length apply.bound_symbols
    then conversion_failure "Set mappings cannot have unbound symbols" apply.node.location
    else if List.exists (fun (b : Xml.bound_symbol) -> b.is_tuple) bound_symbols
    (* Set mapping that includes at least one tuple *)
    then SetOfTuply (
      convert_expression body,
      List.map (convert_tuply_bounds apply.node) bound_symbols |> List.flatten
    )
    (* Set mapping without any tuples *)
    else SetOf (
      convert_expression body,
      List.map (convert_non_tuply_bounds apply.node) bound_symbols |> List.flatten
    )
  | _ -> conversion_failure "Invalid number of bounds or operands to set mapping" apply.node.location
) |> attach_props apply.node

(** Conversion of expressions of the form {x \in S : P(x)} or {<<x, y>> \in S \X T : P(x, y)}
*)
and convert_set_filter (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | [Bound {symbol_refs = [symbol_ref]; is_tuple = false; expression}], [Expression predicate] -> SetSt (
    resolve_bound_symbol symbol_ref,
    convert_expression expression,
    convert_expression predicate
  )
  | [Bound {symbol_refs = (_ :: _) as symbol_refs; is_tuple = true; expression}], [Expression predicate] -> SetStTuply (
    List.map resolve_bound_symbol symbol_refs,
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
and convert_recursive_function (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | Unbound function_name :: (_ :: _ as all_bound_symbols), [Expression body] ->
    let bound_symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Bound b -> Some b | _ -> None) all_bound_symbols in
    if List.length bound_symbols <> List.length all_bound_symbols
    then conversion_failure "Function definitions cannot have unbound symbols" apply.node.location
    else if List.exists (fun (b : Xml.bound_symbol) -> b.is_tuple) bound_symbols
    (* Function definition bounds that include at least one tuple *)
    then FcnTuply (List.map (convert_tuply_bounds apply.node) bound_symbols |> List.flatten, convert_expression body)
    (* Function definition bounds without any tuples *)
    else Fcn (List.map (convert_non_tuply_bounds apply.node) bound_symbols |> List.flatten, convert_expression body)
  | _ -> conversion_failure "Invalid number of bounds or operands to recursive function definition" apply.node.location
) |> attach_props apply.node

(** Converts function construction expressions like [x \in S, y \in P |-> x + y];
    also handles record construction, like [x |-> expr1, y |-> expr2].
*)
and convert_function_constructor (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | _ :: _, [Expression body] ->
    let bound_symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Bound b -> Some b | _ -> None) apply.bound_symbols in
    if List.length bound_symbols <> List.length apply.bound_symbols
    then conversion_failure "Function definitions cannot have unbound symbols" apply.node.location
    else if List.exists (fun (b : Xml.bound_symbol) -> b.is_tuple) bound_symbols
    (* Function definition bounds that include at least one tuple *)
    then FcnTuply (List.map (convert_tuply_bounds apply.node) bound_symbols |> List.flatten, convert_expression body)
    (* Function definition bounds without any tuples *)
    else Fcn (List.map (convert_non_tuply_bounds apply.node) bound_symbols |> List.flatten, convert_expression body)
  | _ -> conversion_failure "Invalid operands to function constructor" apply.node.location
) |> attach_props apply.node

(** Converts function set expressions of the form [P -> Q]
*)
and convert_function_set (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | [], [Expression domain; Expression range] ->
    Arrow (convert_expression domain, convert_expression range)
  | _ -> conversion_failure "Invalid operands to function set expression" apply.node.location
) |> attach_props apply.node

(** Conversion of function application, like f[x, y, z].
*)
and convert_function_application (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | [], Expression fn :: all_args ->
    let args = apply.operands |> as_expr_ls __FUNCTION__ apply.node.location |> List.map convert_expression in
    FcnApp (convert_expression fn, args)
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
  | [], (_ :: _ as pairs) ->
    let mk_field (operand : Xml.expression) : (string * Expr.T.expr) option =
      match operand with
      | OpApplNode {operator; bound_symbols = []; operands = [Expression StringNode {value}; Expression right]} -> (
        match (resolve_ref operator).kind with
        | BuiltInKind {name = "$Pair"} -> Some (value, convert_expression right)
        | _ -> None
      ) | _ -> None
    in let fields = pairs |> as_expr_ls __FUNCTION__ apply.node.location |> List.filter_map mk_field in
    if List.length fields <> List.length pairs
    then conversion_failure "Invalid operands to record operator; expected pairs of expressions" apply.node.location
    else constructor fields
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
        match (resolve_ref operator).kind, (resolve_ref update_op).kind with
        | BuiltInKind {name = "$Pair"}, BuiltInKind {name = "$Seq"} ->
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

(** Conversion of expression CASE p1 -> e1 [] p2 -> e2 [] ... [] OTHER -> e

    TODO: SANY XML exporter cannot currently handle OTHER branches; see:
    https://github.com/tlaplus/tlaplus/issues/1291
*)
and convert_case (apply : Xml.op_appl_node) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | [], (_ :: _ as pairs) ->
    let mk_case (operand : Xml.expr_or_op_arg) : (Expr.T.expr * Expr.T.expr) option =
      match operand with
      | Expression OpApplNode {operator; bound_symbols = []; operands = [Expression cond; Expression result]} -> (
        match (resolve_ref operator).kind with
        | BuiltInKind {name = "$Pair"} -> Some (convert_expression cond, convert_expression result)
        | _ -> None
      ) | _ -> None
    in let cases = List.filter_map mk_case pairs in
    if List.length cases <> List.length pairs
    then conversion_failure "Invalid operands to CASE; expected pairs of expressions" apply.node.location
    else Case (cases, None)
  | _ -> conversion_failure "Invalid bound symbols or operands to CASE" apply.node.location
) |> attach_props apply.node

(** Conversion of application of user-defined operators, including operators
    defined in the standard modules.
*)
and convert_user_defined_op_appl (apply : Xml.op_appl_node) (op : Xml.user_defined_op_kind) : Expr.T.expr =
  Apply (
    Opaque op.name |> attach_props op.node,
    List.map convert_expression_or_operator_argument apply.operands
  ) |> attach_props apply.node

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
      List.map convert_expression_or_operator_argument apply.operands
    ) |> attach_props apply.node

(** Conversion of reference to module-level constants or variables. Again
    information is lost and the string will need to be resolved into a De
    Bruijn index later on.
*)
and convert_op_decl_node_op_appl (apply : Xml.op_appl_node) (decl : Xml.op_decl_node) : Expr.T.expr =
  match decl.arity with
  | 0 -> Opaque decl.name |> attach_props decl.node
  | n -> Apply (
      Opaque decl.name |> attach_props decl.node,
      List.map convert_expression_or_operator_argument apply.operands
    ) |> attach_props apply.node

(** OpApplNode is a very general node used by SANY to represent essentially
    all expression types. Things like \A x \in S : P are represented as an
    application of the built-in "forall" operator, with argument P and symbol
    x bound by S. This complicated method de-abstracts this into the more
    detailed Expr.T.expr variant type used by TLAPS.
*)
and convert_op_appl_node (apply : Xml.op_appl_node) : Expr.T.expr =
  let op_kind = (resolve_ref apply.operator).kind in
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
  | TheoremDefNode thm -> Opaque thm.name |> attach_props thm.node
  | _ -> conversion_failure ("Invalid operator reference in OpApplNode : " ^ (Xml.show_entry_kind op_kind)) apply.node.location

(** Some places in TLA⁺ syntax allow both normal expressions and also
    operators. Mainly this occurs when applying an operator that could accept
    another operator as a parameter. So any time the user calls an operator
    like op(x, y, z), x, y, and z can each be either expressions or operator
    references. LAMBDA operators can also appear here.
*)
and convert_expression_or_operator_argument (op_expr : Xml.expr_or_op_arg) : Expr.T.expr =
  match op_expr with
  | Expression expr -> convert_expression expr
  | OpArg uid -> match (resolve_ref uid).kind with
    | FormalParamNode param -> Opaque param.name |> attach_props param.node
    | UserDefinedOpKind userdef -> Opaque userdef.name |> attach_props userdef.node
    | BuiltInKind builtin -> (match try_convert_builtin builtin with
      | Some b -> Internal b |> attach_props builtin.node
      | None -> todo "Built-in operator argument" builtin.name builtin.node.location)
    | OpDeclNode decl -> Opaque decl.name |> attach_props decl.node
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
  | NumeralNode n -> Num (Int.to_string n.value, "") |> attach_props n.node
  | StringNode s -> String s.value |> attach_props s.node
  | OpApplNode apply -> convert_op_appl_node apply
  | LetInNode let_in -> convert_let_in_node let_in
  | LabelNode label -> convert_label label
  (* TODO: true means @ from EXCEPT, false means @ from proof step (???) *)
  | AtNode at_node -> At true |> attach_props at_node.node

and convert_label (label : Xml.label_node) : Expr.T.expr = (
  match label.body with
  | Expression expr -> Parens (convert_expression expr, noprops Syntax)
  | AssumeProve ap -> Parens (Sequent (convert_assume_prove ap) |> noprops, noprops Syntax)
) |> attach_props label.node

and convert_let_in_node ({node; def_refs; body} : Xml.let_in_node) : Expr.T.expr =
  let definitions = List.map (fun ref ->
    match (resolve_ref ref).kind with
    | UserDefinedOpKind op -> convert_user_defined_op_kind op
    | _ -> todo "LET/IN definition" "Probably an instance" None
  ) def_refs in
  Let (definitions, convert_expression body) |> attach_props node

(** Converts user-defined operators defined within LET/IN expressions.
*)
and convert_user_defined_op_kind (xml : Xml.user_defined_op_kind) : Expr.T.defn =
  let name = attach_props xml.node xml.name in
  let body = xml.body |> convert_expression in
  (* TLAPS represents op(x) == expr as op == LAMBDA x : expr *)
  let expr = match xml.params with
  | [] -> body
  | params -> Lambda (List.map resolve_leibniz_formal_param_node params, body) |> attach_props xml.node
  in Operator (name, expr) |> attach_props xml.node

(** Converts user-defined operators defined in a module top-level.
*)
and convert_unit_user_defined_op_kind (xml: Xml.user_defined_op_kind) : Module.T.modunit =
  match xml.recursive with
  | true -> conversion_failure "TLAPS does not yet support recursive operators" xml.node.location
  | false -> (Definition (
      convert_user_defined_op_kind xml,
      User,
      Hidden, (* If Visible, will be auto-included in all BY proofs *)
      Export (* Whether definition is declared LOCAL *)
    )) |> attach_props xml.node

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
    Option.map (fun uid -> let def = resolve_theorem_def_node uid in attach_props def.node def.name) thm.definition,
    convert_sequent thm.body,
    0 (* The purpose of this integer parameter is unknown. *),
    proof,
    proof,
    empty_summary
  ) |> attach_props thm.node

and convert_assume_prove (ap : Xml.assume_prove_node) : sequent = {
  context = Deque.empty; (* TODO: fill in context from ASSUME part *)
  active = convert_expression ap.prove;
}

(** Sequents are theorem bodies, which are either simple expressions or
    ASSUME/PROVE constructs.
    TODO: handle ASSUME/PROVE
*)
and convert_sequent (seq : Xml.expr_or_assume_prove) : sequent =
  match seq with
  | Expression expr -> {context = Deque.empty; active = convert_expression expr}
  | AssumeProve ap -> convert_assume_prove ap

(** Converts a proof, which can either be OMITTED, OBVIOUS, BY, or a series
    of individual proof steps culminated in a QED step.
*)
and convert_proof (uid : int) (previous_proof_level : int) (proof : Xml.proof_node_group option) : Proof.T.proof =
  match proof with
  | None -> Omitted Implicit |> noprops |> attach_proof_step_name (Unnamed (previous_proof_level + 1, uid))
  | Some Omitted node -> Omitted Explicit |> attach_props node |> attach_proof_step_name (Unnamed (previous_proof_level + 1, uid))
  | Some Obvious node -> Obvious |> attach_props node |> attach_proof_step_name (Unnamed (previous_proof_level + 1, uid))
  | Some By proof -> convert_by_proof proof |> attach_proof_step_name (Unnamed (previous_proof_level + 1, uid))
  | Some Steps proof -> convert_proof_steps uid previous_proof_level proof

(** Converts proofs of the form BY x, y, z DEF a, b, c. This is another place
    where information is lost, as the facts and definitions are converted to
    strings that will need to be resolved to De Bruijn indices later on.
*)
and convert_by_proof ({node; facts; defs} : Xml.by_proof_node) : Proof.T.proof =
  By ({
    facts = List.map convert_expression facts;
    defs = List.map (resolve_def node) defs;
  },
  true (* This should be true if the ONLY keyword is present *)
) |> attach_props node

(** One possible proof form is a series of steps, culminating in a QED step.
    This method converts that structure. This is the most complex part of the
    proof conversion, primarily due to the necessity of appending proof step
    names and levels to each step and overall proof. SANY does not export the
    proof level in its parse tree, and looking at the code on that side there
    does not seem to be an easy method of doing so. Thus we have to parse the
    first proof step name to get the initial proof level, which might be <*>
    or <+> and thus relative to the previous proof level. This information is
    propagated both up & down the parse tree to assign correct proof levels
    elsewhere. Proof names can be either named or unnamed; in the latter case
    TLAPM requires a unique ID to be assigned, so we use the UID of the SANY
    AST node.
*)
and convert_proof_steps (uid : int) (previous_proof_level : int) ({node; steps} : Xml.steps_proof_node) : Proof.T.proof =
  (* Splits the proof steps into ordinary proof steps and a final QED step. *)
  let split_steps (steps : Xml.proof_step_group list) : (Xml.proof_step_group list * int) =
    match List.rev steps with
    | [] -> conversion_failure "Step-based proofs must have at least one step" node.location
    | TheoremNodeRef uid :: rest -> (List.rev rest, uid)
    | _ -> conversion_failure "Final (QED) step of a step-based proof must be a theorem reference" node.location
  in let convert_qed_step (proof_level : proof_level) (uid : int) : Proof.T.qed_step * proof_level =
    let thm = resolve_theorem_node uid in
    let step_name = convert_proof_step_name uid proof_level thm.definition in
    let qed_step = Qed (convert_proof uid (step_number step_name) thm.proof) |> attach_props thm.node in
    attach_proof_step_name step_name qed_step, Known (step_number step_name)
  in let steps, qed = split_steps steps
  in let steps, proof_level = List.fold_left convert_proof_step ([], Previous previous_proof_level) steps
  in let qed_step, proof_level = convert_qed_step proof_level qed
  in let proof_level = match proof_level with
   | Previous _ -> conversion_failure "Current proof level should be known after processing all steps" node.location
   | Known n -> n
  in Steps (List.rev steps, qed_step)
  |> attach_props node
  |> attach_proof_step_name (Unnamed (proof_level, uid))

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

    This function has an odd type signature because it's intended for use in
    a List.fold_left over the list of proof steps; the reason we need to do
    this is to identify the proof level of this proof by parsing the actual
    proof step names, then propagating this knowledge forward in the fold.
    The resulting list of proof steps is returned in reverse order, and must
    be reversed to be in the correct order for TLAPM.
*)
and convert_proof_step (steps, proof_level : Proof.T.step list * proof_level) (step : Xml.proof_step_group) : Proof.T.step list * proof_level =
  match step with
  | InstanceNode {node} -> conversion_failure "INSTANCE proof steps are deprecated from the TLA+ language standard" node.location
  | TheoremNode -> todo "TheoremNode proof step" "" None
  (* TODO: attach name to DefStep step *)
  | DefStep {node; def_refs} ->
    let step = Define (def_refs |> List.map resolve_user_defined_op_kind |> List.map convert_user_defined_op_kind) |> attach_props node in
    step :: steps, proof_level
  (* TODO: confirm boolean parameter corresponds to ONLY keyword *)
  (* TODO: attach name to UseOrHide step *)
  | UseOrHide use_or_hide -> (Use (convert_usable use_or_hide, use_or_hide.only) |> attach_props use_or_hide.node) :: steps, proof_level
  | TheoremNodeRef uid ->
    let is_op (uid : int) (op_name : string) : bool =
      match (resolve_ref uid).kind with
      | BuiltInKind op when op.name = op_name -> true
      | _ -> false
    in let thm = resolve_theorem_node uid in
    let step_name = convert_proof_step_name uid proof_level thm.definition in
    let step = match thm.body with
    | Expression OpApplNode {operands = [Expression expr]; operator} when is_op operator "$Pfcase" ->
        Pcase (convert_expression expr, convert_proof uid (step_number step_name) thm.proof) |> attach_props thm.node
    | _ -> Suffices (convert_sequent thm.body, convert_proof uid (step_number step_name) thm.proof) |> attach_props thm.node
    in attach_proof_step_name step_name step :: steps, Known (step_number step_name)

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
  if ast.modules <> [] then conversion_failure "SANY AST cannot have multiple top-level modules" None;
  entries :=
    List.fold_left
      (fun m (e : Xml.entry) -> Coll.Im.add e.uid e.kind m)
      Coll.Im.empty
      ast.context;
  let ctx : Module.T.modctx = List.fold_left
    (fun (map : Module.T.modctx) (mule_ref : int) ->
      let mule : Xml.module_node = mule_ref |> resolve_module_node in
      if Coll.Sm.mem mule.name map then map
      else Coll.Sm.add mule.name (convert_module_node mule) map
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
