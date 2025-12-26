let convert_ast (ast : Xml.modules) : Module.T.modctx * Module.T.mule =
  let open Util.Coll in
  let open Property in
  let open Module.T in
  (Sm.empty, noprops {
    name = noprops "Placeholder";
    extendees = [];
    instancees = [];
    body = [];
    defdepth = 0;
    stage = Parsed;
    important = true
  })

let parse (module_path : string) : (Module.T.modctx * Module.T.mule, (string option * string)) result =
  match module_path |> Xml.get_module_ast_xml with
  | Error msg -> Error (None, msg)
  | Ok ast -> ast |> convert_ast |> Result.ok
