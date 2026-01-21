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
  file = filename;
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
    | _ -> failwith (Format.sprintf "Invalid character '%c' in proof step name '%s' at parsing state %d" c proof_name parse_state)
  in let (_, level, name) = String.fold_left parse_name (0, [], []) proof_name
  in let digits_to_int (digits : char list) : int =
    List.fold_right (fun (d : char) (acc : int) : int -> (int_of_char d - int_of_char '0') + acc * 10) digits 0
  in let level = match level, proof_level with
  | ['+'], Previous n -> n + 1
  | ['+'], Known _ -> failwith "Cannot have explicit proof level followed by <+>"
  | ['*'], Previous n -> n + 1
  | ['*'], Known n -> n
  | digits, Previous _ -> digits_to_int digits
  | digits, Known n ->
    let level = digits_to_int digits in
    if level <> n then failwith ("Mismatched proof level: expected " ^ string_of_int n ^ " but got " ^ string_of_int level)
    else level
  in if name = [] then Unnamed (level, uid) else
  Named (level, name |> List.rev |> List.to_seq |> String.of_seq, false)

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
let resolve_ref (uid : int) : Xml.entry =
  match Coll.Im.find_opt uid !entries with
  | Some kind -> {uid; kind}
  | None -> failwith ("Unresolved reference to entry UID: " ^ string_of_int uid)

(** A typed version of resolve_ref for module nodes.
*)
let resolve_module_node (uid : int) : Xml.module_node =
  match (resolve_ref uid).kind with
  | ModuleNode mule -> mule
  | _ -> failwith ("Expected module node for UID: " ^ string_of_int uid)

(** A typed version of resolve_ref for operator parameter nodes.
*)
let resolve_formal_param_node (param : Xml.leibniz_param) : (hint * shape) =
  match (resolve_ref param.ref).kind with
  | Xml.FormalParamNode xml -> (
    attach_props xml.node xml.name,
    match xml.arity with
    | 0 -> Shape_expr
    | n -> Shape_op n
  )
  | _ -> failwith ("Expected formal parameter node for UID: " ^ string_of_int param.ref)

(** A typed version of resolve_ref for theorem definition nodes.
*)
let resolve_theorem_def_node (uid : int) : Xml.theorem_def_node =
  match (resolve_ref uid).kind with
  | TheoremDefNode xml -> xml
  | _ -> failwith ("Expected theorem definition node for UID: " ^ string_of_int uid)

(** A typed version of resolve_ref for theorem nodes.
*)
let resolve_theorem_node (uid : int) : Xml.theorem_node =
  match (resolve_ref uid).kind with
  | TheoremNode xml -> xml
  | _ -> failwith ("Expected theorem node for UID: " ^ string_of_int uid)

(** A typed version of resolve_ref for bound symbols.
*)
let resolve_bound_symbol (uid : int) : hint =
  match Coll.Im.find_opt uid !entries with
  | Some (Xml.FormalParamNode ({arity = 0} as xml)) -> attach_props xml.node xml.name
  | Some (Xml.FormalParamNode _) -> failwith ("Bound symbol cannot be an operator: " ^ string_of_int uid)
  | _ -> failwith ("Unresolved formal parameter node UID: " ^ string_of_int uid)

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
  | "UNCHANGED" -> Some Builtin.UNCHANGED
  | "'" -> Some Builtin.Prime
  | "[]" -> Some (Builtin.Box false)
  | "=" -> Some Builtin.Eq
  | "\\in" -> Some Builtin.Mem
  | "\\notin" -> Some Builtin.Notmem
  | "\\land" -> Some Builtin.Conj
  | "=>" -> Some Builtin.Implies
  | "\\equiv" -> Some Builtin.Equiv
  | _ -> None

(** Converts a top-level module node. *)
let rec convert_module_node (mule : Xml.module_node) : Module.T.mule =
  let inline_unit unit =
    match unit with
    | `Ref uid -> resolve_ref uid
    | `OtherTODO name -> todo "Module unit" (name ^ " unit not yet supported") None
  (** Converts an entry, which is an abstract type that can be all sorts of
      things; SANY heavily uses GUIDs to reference one entity from another and
      those GUIDs are resolved in a global table with no real type information.
      Thus in-scope operator parameters coexist alongside entire modules, and
      here we branch out to the appropriate conversion method.
  *)
  in let convert_entry (entry : Xml.entry) : Module.T.modunit =
    match entry.kind with
    | ModuleNode submod -> Submod (convert_module_node submod) |> attach_props submod.node
    | OpDeclNode op_decl_node -> convert_op_decl_node op_decl_node
    | UserDefinedOpKind user_defined_op_kind -> convert_user_defined_op_kind user_defined_op_kind
    | BuiltInKind built_in_kind -> convert_built_in_kind built_in_kind
    | FormalParamNode formal_param_node -> convert_formal_param_node formal_param_node
    | TheoremDefNode theorem_def_node -> convert_theorem_def_node theorem_def_node
    | TheoremNode theorem_node -> convert_theorem_node entry.uid 0 theorem_node
  in {
    name = noprops mule.name;
    extendees = [];
    instancees = [];
    body = mule.units |> List.map inline_unit |> List.map convert_entry;
    defdepth = 0;
    stage = Parsed;
    important = false
  } |> attach_props mule.node

(** Converts operator declarations such as CONSTANTS and VARIABLES. In a
    declaration like VARIABLES x, y, z, each of x, y, and z are given as
    separate OpDeclNode entries. In contrast, TLAPM wraps all of these in a
    single Variables modunit.
*)
and convert_op_decl_node (xml : Xml.op_decl_node) : Module.T.modunit =
  match xml.kind with
  | Variable -> noprops (Variables [attach_props xml.node xml.name])

(** Converts action-level expressions such as [][expr]_sub and <><<expr>>_sub.
*)
and convert_action_expr (op : modal_op) (apply : Xml.op_appl_node) : Expr.T.expr =
  match apply.operands with
  | [expr; sub] -> Sub (
    op,
    convert_expression_or_operator_argument expr,
    convert_expression_or_operator_argument sub
  ) |> attach_props apply.node
  | _ -> failwith "Wrong number of operands to action expression"

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
  | [Bound {is_tuple = false; symbol_refs = [param]; expression}], [body] ->
    Choose (
      resolve_bound_symbol param,
      Some (convert_expression expression),
      convert_expression_or_operator_argument body
    )
  (* Case 2: Bounded tuple CHOOSE expression *)
  | [Bound ({is_tuple = true} as symbol)], [body] ->
    ChooseTuply (
      List.map resolve_bound_symbol symbol.symbol_refs,
      Some (convert_expression symbol.expression),
      convert_expression_or_operator_argument body
    )
  (* Case 3: Unbounded non-tuple CHOOSE expression *)
  | [Unbound ({is_tuple = false} as symbol)], [body] ->
    Choose (
      resolve_bound_symbol symbol.symbol_ref,
      None,
      convert_expression_or_operator_argument body
    )
  (* Case 4: Unbounded tuple CHOOSE expression *)
  | Unbound {is_tuple = true} :: _, [body] ->
    let symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Unbound ({is_tuple = true} as u) -> Some u | _ -> None) apply.bound_symbols in
    if List.length symbols <> List.length apply.bound_symbols
    then failwith "Inconsistent bound/unbound or tuple/non-tuple symbols in CHOOSE"
    else ChooseTuply (
      List.map (fun (s : Xml.unbound_symbol) -> resolve_bound_symbol s.symbol_ref) symbols,
      None,
      convert_expression_or_operator_argument body
    )
  | _ -> failwith "Invalid number of bounds or operands to CHOOSE"
) |> attach_props apply.node

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
and convert_quantification (quant : Expr.T.quantifier) (apply : Xml.op_appl_node) (op : Xml.built_in_kind) : Expr.T.expr = (
  match apply.bound_symbols, apply.operands with
  | _ :: _, [body] ->
    let bound_symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Bound b -> Some b | _ -> None) apply.bound_symbols in
    let unbound_symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Unbound b -> Some b | _ -> None) apply.bound_symbols in
    if unbound_symbols <> []
    then
      if bound_symbols <> []
      then failwith "Cannot mix bound and unbound symbols in quantification"
      else if List.exists (fun (b : Xml.unbound_symbol) -> b.is_tuple) unbound_symbols
      then failwith "Unbounded tuple quantification is not supported"
      (* Unbounded quantification *)
      else let mk_bound (bound : Xml.unbound_symbol) : bound = (
        resolve_bound_symbol bound.symbol_ref,
        Unknown, (* TODO: figure out purpose of this parameter *)
        No_domain
      ) in Quant (
        quant,
        List.map mk_bound unbound_symbols,
        convert_expression_or_operator_argument body
      )
    else if List.exists (fun (b : Xml.bound_symbol) -> b.is_tuple) bound_symbols
    (* Bounded quantification that includes at least one tuple *)
    then let mk_bounds (bound : Xml.bound_symbol) : tuply_bounds =
      if bound.is_tuple
      then match List.map resolve_bound_symbol bound.symbol_refs with
      | (_ :: _ as symbols) -> [(Bound_names symbols, Domain (convert_expression bound.expression))]
      | [] -> failwith "Tuple bound symbol groups must have at least one symbol"
      else match List.map resolve_bound_symbol bound.symbol_refs with
      | hd :: tl -> (Bound_name hd, Domain (convert_expression bound.expression))
        :: List.map (fun s -> (Bound_name s, Ditto)) tl
      | [] -> failwith "Bound symbol groups must have at least one symbol"
    in QuantTuply (
      quant,
      List.map mk_bounds bound_symbols |> List.flatten,
      convert_expression_or_operator_argument body
    )
    (* Bounded quantification without any tuples *)
    else let mk_bounds (bound : Xml.bound_symbol) : bounds =
      match List.map resolve_bound_symbol bound.symbol_refs with
      | hd :: tl -> (hd, Unknown, Domain (convert_expression bound.expression))
        :: List.map (fun s -> (s, Unknown, Ditto)) tl
      | [] -> failwith "Bound symbol groups must have at least one symbol"
    in Quant (
      quant,
      List.map mk_bounds bound_symbols |> List.flatten,
      convert_expression_or_operator_argument body
    )
  | _ -> failwith "Invalid number of bounds or operands to quantification"
) |> attach_props apply.node

(** Conversion of application of all traditional built-in operators like = or
    \cup but also things like CHOOSE and \A which one would ordinarily not
    view as built-in operators.
*)
and convert_built_in_op_appl (apply : Xml.op_appl_node) (op : Xml.built_in_kind) : Expr.T.expr =
  match try_convert_builtin op with
  (* Traditional built-in operators *)
  | Some builtin -> Apply (
      Internal builtin |> attach_props op.node,
      List.map convert_expression_or_operator_argument apply.operands
    ) |> attach_props apply.node
  (* More abstract kinds of built-in operators *)
  | None -> (
      match op.name with
      | "$SetEnumerate" -> SetEnum (
        List.map convert_expression_or_operator_argument apply.operands
      ) |> attach_props apply.node
      | "$Tuple" -> Tuple (
        List.map convert_expression_or_operator_argument apply.operands
      ) |> attach_props apply.node
      | "$BoundedChoose" -> convert_choose apply
      | "$UnboundedChoose" -> convert_choose apply
      | "$SquareAct" -> convert_action_expr Box apply
      | "$BoundedExists" -> convert_quantification Exists apply op
      | "$BoundedForall" -> convert_quantification Forall apply op
      | "$UnboundedExists" -> convert_quantification Exists apply op
      | "$UnboundedForall" -> convert_quantification Forall apply op
      | s -> todo "Built-in operator" s apply.node.location
    )

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
  | _ -> failwith ("Invalid operator reference in OpApplNode : " ^ (Xml.show_entry_kind op_kind) )

(** Some places in TLA⁺ syntax allow both normal expressions and also
    operators. Mainly this occurs when applying an operator that could accept
    another operator as a parameter. So any time the user calls an operator
    like op(x, y, z), x, y, and z can each be either expressions or operator
    references. LAMBDA operators can also appear here.
*)
and convert_expression_or_operator_argument (op_expr : Xml.expr_or_op_arg) : Expr.T.expr =
  match op_expr with
  | Expression expr -> convert_expression expr
  (* TODO: add support for operators here *)

(** Converts a basic expression type, which will be either a primitive value
    or an operator application.
*)
and convert_expression (expr : Xml.expression) : Expr.T.expr =
  match expr with
  | NumeralNode expr -> Num (Int.to_string expr.value, "") |> attach_props expr.node
  | OpApplNode apply -> convert_op_appl_node apply

(** Converts user-defined operators defined in a module top-level or within
    LET/IN expressions.
*)
and convert_user_defined_op_kind (xml: Xml.user_defined_op_kind) : Module.T.modunit =
  match xml.recursive with
  | true -> failwith "TLAPS does not yet support recursive operators"
  | false -> noprops (Definition (
      Operator (
        attach_props xml.node xml.name,
        let expr = xml.body |> convert_expression in
        match xml.params with
        | [] -> expr
        (* TLAPS represents op(x) == expr as op == LAMBDA x : expr *)
        | params -> Lambda (List.map resolve_formal_param_node params, expr) |> noprops
      ) |> noprops,
      User,
      Visible,
      Export
    ))

and convert_built_in_kind (built_in_kind : Xml.built_in_kind) : Module.T.modunit =
  todo "BuiltInKind" "" built_in_kind.node.location

and convert_formal_param_node (formal_param_node : Xml.formal_param_node) : Module.T.modunit =
  todo "FormalParamNode" "" formal_param_node.node.location

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
    oddities in the form of additional metadata.
*)
and convert_theorem_node (uid : int) (previous_proof_level : int) (thm : Xml.theorem_node) : Module.T.modunit =
  Theorem (
    Option.map (fun uid -> let def = resolve_theorem_def_node uid in attach_props def.node def.name) thm.definition,
    convert_sequent thm.body,
    0 (* TODO figure out what this integer parameter means *),
    convert_proof uid previous_proof_level thm.proof,
    noprops Obvious, (* TODO figure out why there are two proofs *)
    empty_summary  (* TODO figure out purpose of summary *)
  ) |> attach_props thm.node

(** Sequents are theorem bodies, which are either simple expressions or
    ASSUME/PROVE constructs.
    TODO: handle ASSUME/PROVE
*)
and convert_sequent (seq : Xml.expr_or_assume_prove) : sequent =
  match seq with
  | Expression expr -> {context = Deque.empty; active = convert_expression expr}

(** Converts a proof, which can either be OMITTED, OBVIOUS, BY, or a series
    of individual proof steps culminated in a QED step.
*)
and convert_proof (uid : int) (previous_proof_level : int) (proof : Xml.proof_node_group) : Proof.T.proof =
  match proof with
  | Omitted node -> Omitted Explicit |> attach_props node |> attach_proof_step_name (Unnamed (previous_proof_level + 1, uid))
  | Obvious node -> Obvious |> attach_props node |> attach_proof_step_name (Unnamed (previous_proof_level + 1, uid)) 
  | By proof -> convert_by_proof proof |> attach_proof_step_name (Unnamed (previous_proof_level + 1, uid))
  | Steps proof -> convert_proof_steps uid previous_proof_level proof

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
  let rec split_steps (steps : Xml.proof_step_group list) : (Xml.proof_step_group list * Xml.proof_step_group) =
    match List.rev steps with
    | [] -> failwith "Step-based proofs must have at least one step"
    | last :: rest -> (List.rev rest, last)
  in let convert_proof_step (steps, proof_level : Proof.T.step list * proof_level) (step : Xml.proof_step_group) : Proof.T.step list * proof_level =
    match step with
    (* TODO: handle other proof step types *)
    | TheoremNodeRef uid ->
      let thm = resolve_theorem_node uid in
      let step_name = convert_proof_step_name uid proof_level thm.definition in
      let step = Suffices (convert_sequent thm.body, convert_proof uid (step_number step_name) thm.proof) |> attach_props thm.node in
      (attach_proof_step_name step_name step :: steps, Known (step_number step_name))
  in let convert_qed_step (proof_level : proof_level) (step : Xml.proof_step_group) : Proof.T.qed_step * proof_level =
    match step with
    (* TODO: handle other proof step types *)
    | TheoremNodeRef uid ->
      let thm = resolve_theorem_node uid in
      let step_name = convert_proof_step_name uid proof_level thm.definition in
      let qed_step = Qed (convert_proof uid (step_number step_name) thm.proof) |> attach_props thm.node in
      (attach_proof_step_name step_name qed_step, Known (step_number step_name))
  in let steps, qed = split_steps steps
  in let steps, proof_level = List.fold_left convert_proof_step ([], Previous previous_proof_level) steps
  in let qed_step, proof_level = convert_qed_step proof_level qed
  in let proof_level = match proof_level with
   | Previous _ -> failwith "Current proof level should be known after processing all steps"
   | Known n -> n
  in Steps (List.rev steps, qed_step)
  |> attach_props node
  |> attach_proof_step_name (Unnamed (proof_level, uid))

(** Converts proofs of the form BY x, y, z DEF a, b, c. This is another place
    where information is lost, as the facts and definitions are converted to
    strings that will need to be resolved to De Bruijn indices later on.
*)
and convert_by_proof ({node; facts; defs} : Xml.by_proof_node) : Proof.T.proof =
  let resolve_def (ref : int) : use_def wrapped =
    match (resolve_ref ref).kind with
    | UserDefinedOpKind op -> Dvar op.name |> attach_props op.node
    | TheoremDefNode thm -> Dvar thm.name |> attach_props thm.node
    | other -> failwith ("Invalid definition reference in BY proof: " ^ (Xml.show_entry_kind other))
  in By ({
    facts = List.map convert_expression facts;
    defs = List.map resolve_def defs;
  },
  true (* TODO: figure out meaning of this parameter *)
) |> attach_props node

(** The top-level method converting the entire SANY AST to TLAPM's AST. SANY
    uses a lot of GUIDs for one entity to reference another, so we load those
    into a global table for fast lookup. This table would have to be a
    parameter to every conversion method in this file; for simplicity we make
    it a module-level mutable variable instead.
*)
let convert_ast (ast : Xml.modules) : (Module.T.modctx * Module.T.mule, (string option * string)) result =
  if ast.modules <> [] then failwith "SANY AST cannot have multiple top-level modules";
  entries :=
    List.fold_left
      (fun m (e : Xml.entry) -> Coll.Im.add e.uid e.kind m)
      Coll.Im.empty
      ast.context;
  let ctx = List.fold_left
    (fun m mule_ref ->
      let mule = mule_ref |> resolve_module_node |> convert_module_node in
      Coll.Sm.add mule.core.name.core mule m)
    Coll.Sm.empty
    ast.module_refs
  in Ok (ctx, Coll.Sm.find ast.root_module ctx)

(** Calls SANY to parse the given module, then converts SANY's AST into the
    TLAPM AST format.
*)
let parse (module_path : string) : (Module.T.modctx * Module.T.mule, (string option * string)) result =
  let ( >>= ) = Result.bind in
  Option.to_result ~none:(None, "TLAPS standard library cannot be found") Params.stdlib_path
  >>= (Xml.get_module_ast_xml module_path)
  >>= convert_ast
