let source_to_sany_xml (module_path : string) : (string, (string * int)) result =
  let open Unix in
  let open Paths in
  let (stdout, stdin, stderr) =
    Unix.open_process_args_full
      "java"
      [|"java"; "-cp"; backend_classpath_string "tla2tools.jar"; "tla2sany.xml.XMLExporter"; "-t"; module_path|]
      (Unix.environment ())
  in let (output, err_output) = (In_channel.input_all stdout, In_channel.input_all stderr) in
  match Unix.close_process_full (stdout, stdin, stderr) with
  | WEXITED 0 -> Ok output
  | WEXITED exit_code -> Error (output ^ err_output, exit_code)
  | _ -> failwith "Process terminated abnormally"

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
  | Error (output, exit_code) -> Error (None, Printf.sprintf "%d\n%s" exit_code output)
  | Ok xml_ast -> xml_ast |> parse_xml |> convert_ast |> Result.ok
