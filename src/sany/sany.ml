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

let entries : Xml.entry_kind Coll.Im.t ref = ref Coll.Im.empty

let converted_modules : Module.T.mule Coll.Im.t ref = ref Coll.Im.empty

let converted_units : Module.T.modunit Coll.Im.t ref = ref Coll.Im.empty

let convert_location (location : Xml.location) : Loc.locus = {
  start = Actual {
    line = location.line.start;
    bol = 0;
    col = location.column.start;
  };
  stop = Actual {
    line = location.line.finish;
    bol = 0;
    col = location.column.finish;
  };
  file = location.filename;
}

let locate_opt (location : Xml.location option) (value : 'a) : 'a wrapped =
  match location with
  | Some loc -> Util.locate value (convert_location loc)
  | None -> noprops value

let locate (value : 'a) (location : Xml.location) : 'a wrapped =
  Util.locate value (convert_location location)

let resolve_ref (uid : int) : Xml.entry =
  match Coll.Im.find_opt uid !entries with
  | Some kind -> {uid; kind}
  | None -> failwith ("Unresolved reference to entry UID: " ^ string_of_int uid)

let resolve_formal_param_node (param : Xml.leibniz_param) : (hint * shape) =
  match Coll.Im.find_opt param.ref.uid !entries with
  | Some (Xml.FormalParamNode xml) -> (
    locate_opt xml.node.location xml.uniquename,
    match xml.arity with
    | 0 -> Shape_expr
    | n -> Shape_op n
  )
  | _ -> failwith ("Unresolved formal parameter node UID: " ^ string_of_int param.ref.uid)

let resolve_bound_symbol (symbol : Xml.formal_param_node_ref) : hint =
  match Coll.Im.find_opt symbol.uid !entries with
  | Some (Xml.FormalParamNode ({arity = 0} as xml)) -> locate_opt xml.node.location xml.uniquename
  | Some (Xml.FormalParamNode _) -> failwith ("Bound symbol cannot be an operator: " ^ string_of_int symbol.uid)
  | _ -> failwith ("Unresolved formal parameter node UID: " ^ string_of_int symbol.uid)

let try_convert_builtin (builtin : Xml.built_in_kind) : Builtin.builtin option =
  match builtin.uniquename with
  | "TRUE" -> Some Builtin.TRUE
  | "FALSE" -> Some Builtin.FALSE
  | "'" -> Some Builtin.Prime
  | "[]" -> Some (Builtin.Box false)
  | "=" -> Some Builtin.Eq
  | "\\in" -> Some Builtin.Mem
  | "\\notin" -> Some Builtin.Notmem
  | "\\land" -> Some Builtin.Conj
  | "=>" -> Some Builtin.Implies
  | "\\equiv" -> Some Builtin.Equiv
  | _ -> None

let rec convert_module_node (uid : int) (mule : Xml.module_node) : Module.T.mule =
  match Coll.Im.find_opt uid !converted_modules with
  | Some kind -> kind
  | None ->
  let inline_unit unit =
    match unit with
    | `Ref uid -> resolve_ref uid
    | `OtherTODO name -> todo "Module unit" (name ^ " unit not yet supported") None
  in locate {
    name = noprops mule.uniquename;
    extendees = [];
    instancees = [];
    body = mule.units |> List.map inline_unit |> List.map convert_entry;
    defdepth = 0;
    stage = Parsed;
    important = true
  } mule.location

and convert_op_decl_node (xml : Xml.op_decl_node) : Module.T.modunit =
  match xml.kind with
  | Variable -> noprops (Variables [locate_opt xml.node.location xml.uniquename])

and convert_action_expr (op : modal_op) (apply : Xml.op_appl_node) : Expr.T.expr =
  match apply.operands with
  | [expr; sub] -> Sub (
    op,
    convert_expression_or_operator_argument expr,
    convert_expression_or_operator_argument sub
  ) |> locate_opt apply.node.location
  | _ -> failwith "Wrong number of operands to $SquareAct"

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
  | [Bound {is_tuple = false; formal_param_node_refs = [param]; expression}], [body] ->
    Choose (
      resolve_bound_symbol param,
      Some (convert_expression expression),
      convert_expression_or_operator_argument body
    )
  (* Case 2: Bounded tuple CHOOSE expression *)
  | [Bound ({is_tuple = true} as symbol)], [body] ->
    ChooseTuply (
      List.map resolve_bound_symbol symbol.formal_param_node_refs,
      Some (convert_expression symbol.expression),
      convert_expression_or_operator_argument body
    )
  (* Case 3: Unbounded non-tuple CHOOSE expression *)
  | [Unbound ({is_tuple = false} as symbol)], [body] ->
    Choose (
      resolve_bound_symbol symbol.formal_param_node_ref,
      None,
      convert_expression_or_operator_argument body
    )
  (* Case 4: Unbounded tuple CHOOSE expression *)
  | Unbound {is_tuple = true} :: _, [body] ->
    let symbols = List.filter_map (fun (s : Xml.symbol) -> match s with | Unbound ({is_tuple = true} as u) -> Some u | _ -> None) apply.bound_symbols in
    if List.length symbols <> List.length apply.bound_symbols
    then failwith "Inconsistent bound/unbound or tuple/non-tuple symbols in CHOOSE"
    else ChooseTuply (
      List.map (fun (s : Xml.unbound_symbol) -> resolve_bound_symbol s.formal_param_node_ref) symbols,
      None,
      convert_expression_or_operator_argument body
    )
  | _ -> failwith "Invalid number of bounds or operands to CHOOSE"
) |> locate_opt apply.node.location

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
        resolve_bound_symbol bound.formal_param_node_ref,
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
      then match List.map resolve_bound_symbol bound.formal_param_node_refs with
      | (_ :: _ as symbols) -> [(Bound_names symbols, Domain (convert_expression bound.expression))]
      | [] -> failwith "Tuple bound symbol groups must have at least one symbol"
      else match List.map resolve_bound_symbol bound.formal_param_node_refs with
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
      match List.map resolve_bound_symbol bound.formal_param_node_refs with
      | hd :: tl -> (hd, Unknown, Domain (convert_expression bound.expression))
        :: List.map (fun s -> (s, Unknown, Ditto)) tl
      | [] -> failwith "Bound symbol groups must have at least one symbol"
    in Quant (
      quant,
      List.map mk_bounds bound_symbols |> List.flatten,
      convert_expression_or_operator_argument body
    )
  | _ -> failwith "Invalid number of bounds or operands to quantification"
) |> locate_opt apply.node.location

(** Conversion of application of all traditional built-in operators like = or
    \cup but also things like CHOOSE and \A which one would ordinarily not
    view as built-in operators.
*)
and convert_built_in_op_appl (apply : Xml.op_appl_node) (op : Xml.built_in_kind) : Expr.T.expr =
  match try_convert_builtin op with
  (* Traditional built-in operators *)
  | Some builtin -> Apply (
      Internal builtin |> locate_opt op.node.location,
      List.map convert_expression_or_operator_argument apply.operands
    ) |> locate_opt apply.node.location
  (* More abstract kinds of built-in operators *)
  | None -> (
      match op.uniquename with
      | "$SetEnumerate" -> SetEnum (
        List.map convert_expression_or_operator_argument apply.operands
      ) |> locate_opt apply.node.location
      | "$Tuple" -> Tuple (
        List.map convert_expression_or_operator_argument apply.operands
      ) |> locate_opt apply.node.location
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
    Opaque "TODO" |> noprops,
    List.map convert_expression_or_operator_argument apply.operands
  ) |> locate_opt apply.node.location

(** Conversion of reference to in-scope operator parameters.
*)
and convert_formal_param_node_op_appl (apply : Xml.op_appl_node) (param : Xml.formal_param_node) : Expr.T.expr =
  match param.arity with
  | 0 -> Opaque param.uniquename |> locate_opt param.node.location
  | n -> Apply (
      Opaque param.uniquename |> locate_opt param.node.location,
      List.map convert_expression_or_operator_argument apply.operands
    ) |> locate_opt apply.node.location

(** Conversion of reference to constants or variables. *)
and convert_op_decl_node_op_appl (apply : Xml.op_appl_node) (decl : Xml.op_decl_node) : Expr.T.expr =
  match decl.arity with
  | 0 -> Opaque decl.uniquename |> locate_opt decl.node.location
  | n -> Apply (
      Opaque decl.uniquename |> locate_opt decl.node.location,
      List.map convert_expression_or_operator_argument apply.operands
    ) |> locate_opt apply.node.location

(** OpApplNode is a very general node used by SANY to represent essentially
    all expression types. Things like \A x \in S : P are represented as an
    application of the built-in "forall" operator, with argument P and symbol
    x bound by S. This complicated method de-abstracts this into the more
    detailed Expr.T.expr type used by TLAPS.
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
  | _ -> failwith ("Invalid operator reference in OpApplNode : " ^ (Xml.show_entry_kind op_kind) )

and convert_expression_or_operator_argument (op_expr : Xml.expr_or_op_arg) : Expr.T.expr =
  match op_expr with
  | Expression expr -> convert_expression expr

and convert_expression (expr : Xml.expression) : Expr.T.expr =
  match expr with
  | NumeralNode expr -> Num (Int.to_string expr.value, "") |> locate_opt expr.node.location
  | OpApplNode apply -> convert_op_appl_node apply

and convert_user_defined_op_kind (xml: Xml.user_defined_op_kind) : Module.T.modunit =
  match xml.recursive with
  | true -> failwith "TLAPS does not yet support recursive operators"
  | false -> noprops (Definition (
      Operator (
        locate_opt xml.node.location xml.uniquename,
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

and convert_theorem_def_node (theorem_def_node : Xml.theorem_def_node) : Module.T.modunit =
  todo "TheoremDefNode" "" theorem_def_node.node.location

and convert_theorem_node (thm : Xml.theorem_node) : Module.T.modunit = Theorem (
  Some (noprops "TODO_thm_name"),
  (match thm.body with
  | Expression expr -> { context = Deque.empty; active = convert_expression expr}),
  0 (* TODO figure out what this integer parameter means *),
  noprops Obvious, (* TODO convert proof *)
  noprops Obvious, (* TODO figure out why there are two proofs *)
  empty_summary  (* TODO figure out purpose of summary *)
) |> locate_opt thm.node.location

and convert_entry (entry : Xml.entry) : Module.T.modunit =
  match entry.kind with
  | ModuleNode mule -> noprops (Submod (convert_module_node entry.uid mule))
  | OpDeclNode op_decl_node -> convert_op_decl_node op_decl_node
  | UserDefinedOpKind user_defined_op_kind -> convert_user_defined_op_kind user_defined_op_kind
  | BuiltInKind built_in_kind -> convert_built_in_kind built_in_kind
  | FormalParamNode formal_param_node -> convert_formal_param_node formal_param_node
  | TheoremDefNode theorem_def_node -> convert_theorem_def_node theorem_def_node
  | TheoremNode theorem_node -> convert_theorem_node theorem_node

let convert_ast (ast : Xml.modules) : (Module.T.modctx * Module.T.mule, (string option * string)) result =
  entries :=
    List.fold_left
      (fun m (e : Xml.entry) -> Coll.Im.add e.uid e.kind m)
      Coll.Im.empty
      ast.context;
  converted_modules := Coll.Im.empty;
  converted_units := Coll.Im.empty;
  let root_module_id, root_module = List.find_map (fun (entry : Xml.entry) ->
      match entry.kind with
      | Xml.ModuleNode mule -> if mule.uniquename = ast.root_module then Some (entry.uid, mule) else None
      | _ -> None) ast.context |> Option.get
  in let root = convert_module_node root_module_id root_module in
  converted_modules := Coll.Im.add root_module_id root !converted_modules;
  Ok (Coll.Sm.empty, root)

let parse (module_path : string) : (Module.T.modctx * Module.T.mule, (string option * string)) result =
  let ( >>= ) = Result.bind in
  Option.to_result ~none:(None, "TLAPS standard library cannot be found") Params.stdlib_path
  >>= (Xml.get_module_ast_xml module_path)
  >>= convert_ast
