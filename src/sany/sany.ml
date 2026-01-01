open Property;;
open Module.T;;
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

let locate_opt (value : 'a) (location : Xml.location option) : 'a wrapped =
  match location with
  | Some loc -> Util.locate value (convert_location loc)
  | None -> noprops value

let locate (value : 'a) (location : Xml.location) : 'a wrapped =
  Util.locate value (convert_location location)

let resolve_ref (uid : int) : Xml.entry =
  match Coll.Im.find_opt uid !entries with
  | Some kind -> {uid; kind}
  | None -> failwith ("Unresolved reference to entry UID: " ^ string_of_int uid)

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

and convert_op_decl_node (node : Xml.op_decl_node) : Module.T.modunit =
  match node.kind with
  | Variable -> noprops (Variables [(locate_opt node.uniquename node.node.location)])

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
