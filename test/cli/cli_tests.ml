(** Unit tests to ensure CLI parameter format does not change.
*)

type setting_value = [
  `B of string * bool ref * bool
  | `I of string * int ref * int
  | `F of string * float ref * float
  | `S of string * string ref * string
  | `SO of string * string option ref * string option
]

let display_setting_value (v : setting_value) : string =
  match v with
  | `B (n, rf, v) -> Printf.sprintf "%s: %b [%b]" n v !rf
  | `I (n, rf, v) -> Printf.sprintf "%s: %d [%d]" n v !rf
  | `F (n, rf, v) -> Printf.sprintf "%s: %f [%f]" n v !rf
  | `S (n, rf, v) -> Printf.sprintf "%s: %s [%s]" n v !rf
  | `SO (n, rf, v) -> Printf.sprintf "%s: %s [%s]" n (Option.value ~default:"None" v) (Option.value ~default:"None" !rf)

let print_setting_diff (formatter : Format.formatter) ((expected, actual) : setting_value * setting_value) : unit =
  if not (expected = actual) then (
    Printf.sprintf "exp/act: (%s)/(%s)" (display_setting_value expected) (display_setting_value actual)
    |> Format.pp_print_text formatter;
  ) else ()

let rec print_setting_list_diff (formatter : Format.formatter) ((expected, actual) : setting_value list * setting_value list) : unit =
  match expected, actual with
  | [], [] -> ()
  | ex :: ex_tl, [] ->
      ex |> display_setting_value |> Printf.sprintf "+exp: %s" |> Format.pp_print_text formatter;
      print_setting_list_diff formatter (ex_tl, []);
  | [], ac :: ac_tl ->
      ac |> display_setting_value |> Printf.sprintf "+act: %s" |> Format.pp_print_text formatter;
      print_setting_list_diff formatter (ac_tl, []);
  | ex :: ex_tl, ac :: ac_tl ->
      print_setting_diff formatter (ex, ac);
      print_setting_list_diff formatter (ex_tl, ac_tl)

let setting_value_changed (setting : setting_value) =
  match setting with
  | `B (_, rf, v) -> not (!rf = v)
  | `I (_, rf, v) -> not (!rf = v)
  | `F (_, rf, v) -> not (!rf = v)
  | `S (_, rf, v) -> not (!rf = v)
  | `SO (_, rf, v) -> not (!rf = v)

let changed_setting_value (setting : setting_value) =
  if setting_value_changed setting then
    match setting with
    | `B (n, rf, _) -> Some (`B (n, rf, !rf))
    | `I (n, rf, _) -> Some (`I (n, rf, !rf))
    | `F (n, rf, _) -> Some (`F (n, rf, !rf))
    | `S (n, rf, _) -> Some (`S (n, rf, !rf))
    | `SO (n, rf, _) -> Some (`SO (n, rf, !rf))
  else None

let set_setting_value (setting : setting_value) =
  match setting with
  | `B (_, rf, v) -> rf := v
  | `I (_, rf, v) -> rf := v
  | `F (_, rf, v) -> rf := v
  | `S (_, rf, v) -> rf := v
  | `SO (_, rf, v) -> rf := v

open Tlapm_lib__Params;;

let setting_values () : setting_value list = [
  `B ("toolbox", toolbox, !toolbox);
  `I ("toolbox_vsn", toolbox_vsn, !toolbox_vsn);
  `B ("use_stdin", use_stdin, !use_stdin);
  `B ("prefer_stdlib", prefer_stdlib, !prefer_stdlib);
  `B ("notl", notl, !notl);
  `B ("verbose", verbose, !verbose);
  `B ("check", check, !check);
  `S ("output_dir", output_dir, !output_dir);
  `I ("wait", wait, !wait);
  `B ("no_fp", no_fp, !no_fp);
  `I ("nofp_sl", nofp_sl, !nofp_sl);
  `I ("nofp_el", nofp_el, !nofp_el);
  `B ("printallobs", printallobs, !printallobs);
  `B ("pr_normal", pr_normal, !pr_normal);
  `B ("ob_flatten", ob_flatten, !ob_flatten);
  `B ("noproving", noproving, !noproving);
  `S ("fp_hist_dir", fp_hist_dir, !fp_hist_dir);
  `I ("fp_original_number", fp_original_number, !fp_original_number);
  `B ("safefp", safefp, !safefp);
  `B ("fp_deb", fp_deb, !fp_deb);
  `B ("use_xtla", use_xtla, !use_xtla);
  `B ("xtla", xtla, !xtla);
  `I ("tb_sl", tb_sl, !tb_sl);
  `I ("tb_el", tb_el, !tb_el);
  `B ("cleanfp", cleanfp, !cleanfp);
  `SO ("fpf_in", fpf_in, !fpf_in);
  `SO ("fpf_out", fpf_out, !fpf_out);
  `B ("fp_loaded", fp_loaded, !fp_loaded);
  `B ("summary", summary, !summary);
  `B ("stats", stats, !stats);
  `B ("keep_going", keep_going, !keep_going);
  `B ("suppress_all", suppress_all, !suppress_all);
  `F ("timeout_stretch", timeout_stretch, !timeout_stretch);
  `F ("backend_timeout", backend_timeout, !backend_timeout);
]

let default_setting_values = setting_values ()

let reset_setting_values () = List.iter set_setting_value default_setting_values

let changed_setting_values () = List.filter_map changed_setting_value default_setting_values

let parse_args (args : string list) : string list * string * string * int option =
  let out = Buffer.create 0 in
  let out_format = Format.formatter_of_buffer out in
  let err = Buffer.create 0 in
  let err_format = Format.formatter_of_buffer err in
  let exception TrappedExit of int in
  let terminate (code : int) = raise (TrappedExit code) in
  try let mods = Tlapm_lib__Tlapm_args.init ~out:out_format ~err:err_format ~terminate:terminate "tlapm" (Array.of_list ("tlapm" :: args)) in
    Format.pp_print_flush out_format ();
    Format.pp_print_flush err_format ();
    (mods, Buffer.contents out, Buffer.contents err, None)
  with TrappedExit exit_code ->
    Format.pp_print_flush out_format ();
    Format.pp_print_flush err_format ();
    ([], Buffer.contents out, Buffer.contents err, Some exit_code)

open OUnit2;;

let test_help _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--help"] in
  assert_equal [] mods;
  assert_equal "" out;
  assert_bool "Should print help text" (String.starts_with err ~prefix:"Usage: tlapm <options> FILE");
  assert_equal (Some 0) exit_code;
  let (mods, out, err, exit_code) = parse_args ["-help"] in
  assert_equal [] mods;
  assert_equal "" out;
  assert_bool "Should print help text" (String.starts_with err ~prefix:"Usage: tlapm <options> FILE");
  assert_equal (Some 0) exit_code;
  assert_equal [] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;;

let test_version _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--version"] in
  assert_equal [] mods;
  assert_equal (rawversion () ^ "\n") out;
  assert_equal "" err;
  assert_equal (Some 0) exit_code;
  assert_equal [] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;;

let test_basic _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["Test.tla"] in
  assert_equal ["Test.tla"] mods;
  assert_equal "" out;
  assert_equal "" err;
  assert_equal None exit_code;
  assert_equal [] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;;

let test_no_mods _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args [] in
  assert_equal [] mods;
  assert_equal "" out;
  assert_bool "Need module req message" (String.starts_with err ~prefix:"Need at least one module file");
  assert_equal (Some 2) exit_code;
  assert_equal [] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;;

let test_verbose _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["-v"; "Test.tla"] in
  assert_equal ["Test.tla"] mods;
  assert_bool "Need config" (String.starts_with out ~prefix:"-------------------- tlapm configuration --------------------");
  assert_equal "" err;
  assert_equal None exit_code;
  assert_equal [`B ("verbose", verbose, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;;
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--verbose"; "Test.tla"] in
  assert_equal ["Test.tla"] mods;
  assert_bool "Need config" (String.starts_with out ~prefix:"-------------------- tlapm configuration --------------------");
  assert_equal "" err;
  assert_equal None exit_code;
  assert_equal [`B ("verbose", verbose, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;;

let test_use_stdin _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--stdin"; "Test.tla"] in
  assert_equal ["Test.tla"] mods;
  assert_equal "" out;
  assert_equal "" err;
  assert_equal None exit_code;
  assert_equal [`B ("use_stdin", use_stdin, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;;

let test_prefer_stdlib _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--prefer-stdlib"; "Test.tla"] in
  assert_equal ["Test.tla"] mods;
  assert_equal "" out;
  assert_equal "" err;
  assert_equal None exit_code;
  assert_equal [`B ("prefer_stdlib", prefer_stdlib, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;;

let cli_test_suite = "Test CLI Parsing" >::: [
  "Help Test" >:: test_help;
  "Basic Test" >:: test_basic;
  "Version Test" >:: test_version;
  "No Mods Test" >:: test_no_mods;
  "Verbose Test" >:: test_verbose;
  "Use Stdin Test" >:: test_use_stdin;
  "Prefer Stdlib Test" >:: test_prefer_stdlib;
];;

let () = run_test_tt_main cli_test_suite
