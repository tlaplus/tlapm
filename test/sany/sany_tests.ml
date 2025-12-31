open Tlapm_lib;;
open Tlapm_lib__Params;;

let _ =
  parser_backend := Sany;
  add_debug_flag "sany";
  match modctx_of_string ~content:"" ~filename:"AddTwo.tla" ~loader_paths:[] ~prefer_stdlib:true with
  | Error (_, msg) -> print_endline msg
  | Ok _ -> print_endline "success"
