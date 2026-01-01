open Property;;
open Module.T;;
open Expr.T;;
open Util;;

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

let try_convert_builtin (builtin : Xml.built_in_kind) : Builtin.builtin option =
  match builtin.uniquename with
  | "=" -> Some Builtin.Eq
  | "TRUE" -> Some Builtin.TRUE
  | "FALSE" -> Some Builtin.FALSE
  | "\\in" -> Some Builtin.Mem
  | "'" -> Some Builtin.Prime
  | "\\land" -> Some Builtin.Conj
  | "[]" -> Some (Builtin.Box false)
  | _ -> None

let rec convert_module_node (uid : int) (mule : Xml.module_node) : Module.T.mule =
  match Coll.Im.find_opt uid !converted_modules with
  | Some kind -> kind
  | None ->
  let inline_unit unit =
    match unit with
    | `Ref uid -> resolve_ref uid
    | `OtherTODO name -> failwith (name ^ " unit not yet supported")
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

(** Conversion of application of all traditional built-in operators like = or
    \cup but also things like CHOOSE and \A which one would ordinarily not
    view as built-in operators. However, the 
*)
and convert_built_in_op_appl (apply : Xml.op_appl_node) (op : Xml.built_in_kind) : Expr.T.expr = (
  match try_convert_builtin op with
  (* Traditional built-in operators *)
  | Some builtin -> Apply (
      Internal builtin |> locate_opt op.node.location,
      List.map convert_expression_or_operator_argument apply.operands
    )
  (* More abstract kinds of built-in operators *)
  | None -> (
      match op.uniquename with
      | "$SetEnumerate" -> SetEnum (List.map convert_expression_or_operator_argument apply.operands)
      | "$UnboundedChoose" -> Choose (noprops "TODO", None, apply.operands |> List.hd |> convert_expression_or_operator_argument)
      | "$Tuple" -> Tuple (List.map convert_expression_or_operator_argument apply.operands)
      | s -> failwith ("Built-in operator application not yet supported: " ^ s)
    )
  ) |> locate_opt apply.node.location

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
  failwith "BuiltInKind conversion not yet supported"

and convert_formal_param_node (formal_param_node : Xml.formal_param_node) : Module.T.modunit =
  failwith "FormalParamNode conversion not yet supported"

and convert_theorem_def_node (theorem_def_node : Xml.theorem_def_node) : Module.T.modunit =
  failwith "TheoremDefNode conversion not yet supported"

and convert_theorem_node (theorem_node : Xml.theorem_node) : Module.T.modunit =
  failwith "TheoremNode conversion not yet supported"

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
