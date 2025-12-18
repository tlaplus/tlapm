open Tlapm_lib;;
open Tlapm_lib__Util;;

let _ =
  let filename = "Test.tla" in
  let file_channel = open_in filename in
  let content = In_channel.input_all file_channel in
  close_in file_channel;
  match modctx_of_string
    ~content
    ~filename
    ~loader_paths:[]
    ~prefer_stdlib:true
  with
  | Ok (mcx, _mule) ->
    Coll.Sm.iter (fun modname _modtree -> print_endline modname) mcx;
  | Error (Some msg, msg2) ->
    print_endline msg;
    print_endline msg2;
  | Error (None, msg) ->
    print_endline msg;