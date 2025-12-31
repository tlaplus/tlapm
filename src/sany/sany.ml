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

let convert_unit_ref (entry_map : Xml.entry_kind Util.Coll.Im.t) (unit_ref : Xml.unit_kind) : modunit = ()

let convert_module_node (entry_map : Xml.entry_kind Util.Coll.Im.t) (mule : Xml.module_node) : Module.T.modunit =
  let loc = convert_location mule.location in
  Util.locate (Submod (Util.locate {
    name = noprops mule.uniquename;
    extendees = [];
    instancees = [];
    body = List.map (convert_unit_ref entry_map) mule.units;
    defdepth = 0;
    stage = Parsed;
    important = true
  } loc)) loc

let convert_op_decl_node (op_decl_node : Xml.op_decl_node) : Module.T.modunit = ()

let convert_user_defined_op_kind (user_defined_op_kind : Xml.user_defined_op_kind) : Module.T.modunit = ()

let convert_built_in_kind (built_in_kind : Xml.built_in_kind) : Module.T.modunit = ()

let convert_formal_param_node (formal_param_node : Xml.formal_param_node) : Module.T.modunit = ()

let convert_theorem_def_node (theorem_def_node : Xml.theorem_def_node) : Module.T.modunit = ()

let convert_theorem_node (theorem_node : Xml.theorem_node) : Module.T.modunit = ()

let convert_entry (entry_map : Xml.entry_kind Util.Coll.Im.t) (entry : Xml.entry) : Module.T.modunit =
  match entry.kind with
  | ModuleNode mule -> convert_module_node entry_map mule
  | OpDeclNode op_decl_node -> convert_op_decl_node op_decl_node
  | UserDefinedOpKind user_defined_op_kind -> convert_user_defined_op_kind user_defined_op_kind
  | BuiltInKind built_in_kind -> convert_built_in_kind built_in_kind
  | FormalParamNode formal_param_node -> convert_formal_param_node formal_param_node
  | TheoremDefNode theorem_def_node -> convert_theorem_def_node theorem_def_node
  | TheoremNode theorem_node -> convert_theorem_node theorem_node

let convert_ast (ast : Xml.modules) : Module.T.modctx * Module.T.mule =
  let entry_map = 
    List.fold_left 
      (fun m (e : Xml.entry) -> Util.Coll.Im.add e.uid e.kind m)
      Util.Coll.Im.empty
      ast.context.entry
  in
  let context = Util.Coll.Sm.empty in
  let _root_module_location = (List.find (fun (m : Xml.module_node) -> m.uniquename = ast.root_module) ast.module_node).location in
  let root_module = noprops {
    name = noprops ast.root_module;
    extendees = [];
    instancees = [];
    body = List.map (convert_entry entry_map) ast.context.entry;
    defdepth = 0;
    stage = Parsed;
    important = true
  } in (context, root_module)

let parse (module_path : string) : (Module.T.modctx * Module.T.mule, (string option * string)) result =
  match module_path |> Xml.get_module_ast_xml with
  | Error msg -> Error (None, msg)
  | Ok ast -> ast |> convert_ast |> Result.ok
