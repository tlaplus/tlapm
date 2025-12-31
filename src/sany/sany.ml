open Property;;
open Module.T;;

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

let resolve_ref (entry_map : Xml.entry_kind Util.Coll.Im.t) (uid : int) : Xml.entry =
  match Util.Coll.Im.find_opt uid entry_map with
  | Some kind -> {uid; kind}
  | None -> failwith ("Unresolved reference to entry UID: " ^ string_of_int uid)

let rec convert_module_node (entry_map : Xml.entry_kind Util.Coll.Im.t) (mule : Xml.module_node) : Module.T.mule =
  let inline_unit unit =
    match unit with
    | `Ref uid -> resolve_ref entry_map uid
    | `OtherTODO name -> failwith (name ^ " unit not yet supported")
  in let loc = convert_location mule.location in
  Util.locate {
    name = noprops mule.uniquename;
    extendees = [];
    instancees = [];
    body = mule.units |> List.map inline_unit |> List.map (convert_entry entry_map);
    defdepth = 0;
    stage = Parsed;
    important = true
  } loc

and convert_op_decl_node (op_decl_node : Xml.op_decl_node) : Module.T.modunit =
  failwith "OpDeclNode conversion not yet supported"

and convert_user_defined_op_kind (user_defined_op_kind : Xml.user_defined_op_kind) : Module.T.modunit =
  failwith "UserDefinedOpKind conversion not yet supported"

and convert_built_in_kind (built_in_kind : Xml.built_in_kind) : Module.T.modunit =
  failwith "BuiltInKind conversion not yet supported"

and convert_formal_param_node (formal_param_node : Xml.formal_param_node) : Module.T.modunit =
  failwith "FormalParamNode conversion not yet supported"

and convert_theorem_def_node (theorem_def_node : Xml.theorem_def_node) : Module.T.modunit =
  failwith "TheoremDefNode conversion not yet supported"

and convert_theorem_node (theorem_node : Xml.theorem_node) : Module.T.modunit =
  failwith "TheoremNode conversion not yet supported"

and convert_entry (entry_map : Xml.entry_kind Util.Coll.Im.t) (entry : Xml.entry) : Module.T.modunit =
  match entry.kind with
  | ModuleNode mule -> noprops (Submod (convert_module_node entry_map mule))
  | OpDeclNode op_decl_node -> convert_op_decl_node op_decl_node
  | UserDefinedOpKind user_defined_op_kind -> convert_user_defined_op_kind user_defined_op_kind
  | BuiltInKind built_in_kind -> convert_built_in_kind built_in_kind
  | FormalParamNode formal_param_node -> convert_formal_param_node formal_param_node
  | TheoremDefNode theorem_def_node -> convert_theorem_def_node theorem_def_node
  | TheoremNode theorem_node -> convert_theorem_node theorem_node

let convert_ast (ast : Xml.modules) : (Module.T.modctx * Module.T.mule, (string option * string)) result =
  print_endline "Starting SANY conversion";
  let entry_map =
    List.fold_left
      (fun m (e : Xml.entry) -> Util.Coll.Im.add e.uid e.kind m)
      Util.Coll.Im.empty
      ast.context.entry
  in
  let module_entries = List.map (fun uid ->
    match Util.Coll.Im.find uid entry_map with
    | Xml.ModuleNode mule -> mule
    | _ -> assert false
  ) ast.module_node_ref in
  let root_module_entry = List.find (fun (m : Xml.module_node) -> String.equal m.uniquename ast.root_module) module_entries in
  let context = Util.Coll.Sm.empty in
  Ok (context, convert_module_node entry_map root_module_entry)
  
let parse (module_path : string) : (Module.T.modctx * Module.T.mule, (string option * string)) result =
  let ( >>= ) = Result.bind in
  Option.to_result ~none:(None, "TLAPS standard library cannot be found") Params.stdlib_path
  >>= (Xml.get_module_ast_xml module_path)
  >>= convert_ast
