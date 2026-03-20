
let find_tla_files dir =
  let cmd = Printf.sprintf "find %s -name '*Test.tla'" (Filename.quote dir) in
  let ic = Unix.open_process_in cmd in
  let rec loop acc =
    match input_line ic with
    | line -> loop (line :: acc)
    | exception End_of_file ->
      ignore (Unix.close_process_in ic);
      List.rev acc
  in
  loop []

open OUnit2;;

let run_test (filename : string) (_ctx: test_ctxt) : unit =
  let open Tlapm_lib in
  let open Stdlib in
  let open Tlapm_lib__Params in
  (*add_debug_flag "sany";*)
  let ic = open_in filename in
  let content = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let check_tlapm (loc, msg) =
    parser_backend := Tlapm;
    match modctx_of_string ~content ~filename ~loader_paths:[] ~prefer_stdlib:true with
    | Error (_, _) -> Printf.eprintf "WARNING: Both SANY and TLAPM failed"
    | Ok _ -> assert_failure (Printf.sprintf "SANY failed, but TLAPM succeeded\n%s\n%s" msg (Option.value ~default:"<no location>" loc))
  in
  parser_backend := Sany;
  try match modctx_of_string ~content ~filename ~loader_paths:[] ~prefer_stdlib:true with
  | Error msg -> check_tlapm msg
  | Ok _ -> ()
  with
  | Failure (msg : string) -> check_tlapm (None, msg)


let mk_test (filepath : string) : test =
  Filename.basename filepath >:: (run_test filepath)

let tests = "SANY semantic escalation tests" >::: (
  find_tla_files "."
  |> List.sort String.compare
  |> List.map mk_test
)

(** The OUnit2 test entrypoint. *)
let () = run_test_tt_main tests
