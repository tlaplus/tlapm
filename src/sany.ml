let source_to_sany_xml (module_path : string) : (string, int) result =
  Error 1

type parsed_xml = unit
let parse_xml (xml_ast : string) : parsed_xml = ()

let convert_ast (ast : parsed_xml) : Module.T.modctx * Module.T.mule =
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

let parse module_path =
  match module_path |> source_to_sany_xml with
  | Error exit_code -> Error (None, Int.to_string exit_code)
  | Ok xml_ast -> xml_ast |> parse_xml |> convert_ast |> Result.ok
