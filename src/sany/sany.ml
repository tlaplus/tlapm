let convert_module_node (mule : Xml.module_node) : Module.T.mule =
  let open Property in
  let open Module.T in
  noprops {
    name = noprops mule.uniquename;
    extendees = [];
    instancees = [];
    body = [];
    defdepth = 0;
    stage = Parsed;
    important = true
  }

let convert_entry (entry : Xml.entry) : Module.T.modunit =
  let open Property in
  let open Module.T in
  match entry.kind with
  | ModuleNode mule -> ()
  | OpDeclNode op_decl_node -> ()
  | UserDefinedOpKind user_defined_op_kind -> ()
  | BuiltInKind built_in_kind -> ()
  | FormalParamNode formal_param_node -> ()
  | TheoremDefNode theorem_def_node -> ()
  | TheoremNode theorem_node -> ()

let convert_ast (ast : Xml.modules) : Module.T.modctx * Module.T.mule =
  let open Property in
  let open Module.T in
  let context = Util.Coll.Sm.empty in
  let _root_module_location = (List.find (fun (m : Xml.module_node) -> m.uniquename = ast.root_module) ast.module_node).location in
  let root_module = noprops {
    name = noprops ast.root_module;
    extendees = [];
    instancees = [];
    body = List.map convert_entry ast.context.entry;
    defdepth = 0;
    stage = Parsed;
    important = true
  } in (context, root_module)

let parse (module_path : string) : (Module.T.modctx * Module.T.mule, (string option * string)) result =
  match module_path |> Xml.get_module_ast_xml with
  | Error msg -> Error (None, msg)
  | Ok ast -> ast |> convert_ast |> Result.ok
