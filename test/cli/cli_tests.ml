(** Unit tests to ensure CLI parameter format does not change.
*)

type setting_value = [
  `B of string * bool ref * bool
  | `I of string * int ref * int
  | `F of string * float ref * float
  | `S of string * string ref * string
  | `SO of string * string option ref * string option
  | `SL of string * string list ref * string list
  | `ML of string * Tlapm_lib__Method.t list ref * Tlapm_lib__Method.t list
]

let capture_output (f : Format.formatter -> unit) : string =
  let out = Buffer.create 0 in
  let out_format = Format.formatter_of_buffer out in
  f out_format;
  Format.pp_print_flush out_format ();
  Buffer.contents out
  

let rec string_contains (needle : string) (haystack : string) : bool =
  match haystack with
  | "" -> false
  | _ -> String.starts_with ~prefix:needle haystack ||
    String.sub haystack 1 ((String.length haystack) - 1) |>
    string_contains needle

let str_ls_as_str (ls : string list) : string =
  "[" ^ (String.concat "; " ls) ^ "]"

let display_setting_value (v : setting_value) : string =
  match v with
  | `B (n, rf, v) -> Printf.sprintf "%s: %b [%b]" n v !rf
  | `I (n, rf, v) -> Printf.sprintf "%s: %d [%d]" n v !rf
  | `F (n, rf, v) -> Printf.sprintf "%s: %f [%f]" n v !rf
  | `S (n, rf, v) -> Printf.sprintf "%s: %s [%s]" n v !rf
  | `SO (n, rf, v) -> Printf.sprintf "%s: %s [%s]" n (Option.value ~default:"None" v) (Option.value ~default:"None" !rf)
  | `SL (n, rf, v) -> Printf.sprintf "%s: %s [%s]" n (str_ls_as_str v) (str_ls_as_str !rf)
  | `ML (n, rf, v) -> Printf.sprintf "%s: %s [%s]" n (str_ls_as_str (List.map (fun m -> capture_output (fun f -> Tlapm_lib__Method.pp_print_tactic f m)) v)) (str_ls_as_str (List.map (fun m -> capture_output (fun f -> Tlapm_lib__Method.pp_print_tactic f m)) !rf))

let print_string_diff (formatter : Format.formatter) ((expected, actual) : string * string) : unit =
  Printf.sprintf "exp/act: (%s)/(%s)" expected actual |> Format.pp_print_text formatter

let rec print_list_diff (formatter : Format.formatter) (expected : 'a list) (actual : 'a list) (as_string : 'a -> string) : unit =
  match expected, actual with
  | [], [] -> ()
  | ex :: ex_tl, [] ->
      ex |> as_string |> Printf.sprintf "+exp: %s" |> Format.pp_print_text formatter;
      print_list_diff formatter ex_tl [] as_string;
  | [], ac :: ac_tl ->
      ac |> as_string |> Printf.sprintf "+act: %s" |> Format.pp_print_text formatter;
      print_list_diff formatter ac_tl [] as_string;
  | ex :: ex_tl, ac :: ac_tl ->
      if not (ex = ac) then print_string_diff formatter (as_string ex, as_string ac);
      print_list_diff formatter ex_tl ac_tl as_string

let print_setting_list_diff (formatter : Format.formatter) ((expected, actual) : setting_value list * setting_value list) : unit =
  print_list_diff formatter expected actual display_setting_value

let print_mod_diff (formatter : Format.formatter) ((expected, actual) : string list * string list) : unit =
  print_list_diff formatter expected actual (fun s -> s)

let setting_value_changed (setting : setting_value) =
  match setting with
  | `B (_, rf, v) -> not (!rf = v)
  | `I (_, rf, v) -> not (!rf = v)
  | `F (_, rf, v) -> not (!rf = v)
  | `S (_, rf, v) -> not (!rf = v)
  | `SO (_, rf, v) -> not (!rf = v)
  | `SL (_, rf, v) -> not (List.equal String.equal !rf v)
  | `ML (_, rf, v) -> not (!rf = v)

let changed_setting_value (setting : setting_value) =
  if setting_value_changed setting then
    match setting with
    | `B (n, rf, _) -> Some (`B (n, rf, !rf))
    | `I (n, rf, _) -> Some (`I (n, rf, !rf))
    | `F (n, rf, _) -> Some (`F (n, rf, !rf))
    | `S (n, rf, _) -> Some (`S (n, rf, !rf))
    | `SO (n, rf, _) -> Some (`SO (n, rf, !rf))
    | `SL (n, rf, _) -> Some (`SL (n, rf, !rf))
    | `ML (n, rf, _) -> Some (`ML (n, rf, !rf))
  else None

let set_setting_value (setting : setting_value) =
  match setting with
  | `B (_, rf, v) -> rf := v
  | `I (_, rf, v) -> rf := v
  | `F (_, rf, v) -> rf := v
  | `S (_, rf, v) -> rf := v
  | `SO (_, rf, v) -> rf := v
  | `SL (_, rf, v) -> rf := v
  | `ML (_, rf, v) -> rf := v

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
  `I ("max_threads", max_threads, !max_threads);
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
  `SL ("rev_search_path", rev_search_path, !rev_search_path);
  `ML ("default_method", default_method, !default_method);
  `S ("smt_logic", smt_logic, !smt_logic);
  `S ("cachedir", cachedir, !cachedir);
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
  assert_equal [] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_bool "Should print help text" (String.starts_with err ~prefix:"Usage: tlapm <options> FILE");
  assert_equal (Some 0) exit_code;
  let (mods, out, err, exit_code) = parse_args ["-help"] in
  assert_equal [] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_bool "Should print help text" (String.starts_with err ~prefix:"Usage: tlapm <options> FILE");
  assert_equal (Some 0) exit_code;
  assert_equal [] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_version _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--version"] in
  assert_equal [] mods ~pp_diff:print_mod_diff;
  assert_equal (rawversion () ^ "\n") out;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal (Some 0) exit_code;
  assert_equal [] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_basic _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_no_mods _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args [] in
  assert_equal [] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_bool "Need module req message" (String.starts_with err ~prefix:"Need at least one module file");
  assert_equal (Some 2) exit_code;
  assert_equal [] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_verbose _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["-v"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_bool "Need config" (String.starts_with out ~prefix:"-------------------- tlapm configuration --------------------");
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("verbose", verbose, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;;
  reset_setting_values ();
  let (mods, out, _err, exit_code) = parse_args ["--verbose"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_bool "Need config" (String.starts_with out ~prefix:"-------------------- tlapm configuration --------------------");
  (* err probably has output due to being unable to find tools; ignore *)
  assert_equal None exit_code;
  assert_equal [`B ("verbose", verbose, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_where _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--where"] in
  assert_equal [] mods ~pp_diff:print_mod_diff;
  assert_bool "Need stlib path" (not (String.equal out ""));
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal (Some 0) exit_code;
  assert_equal [] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_config _test_ctxt =
  reset_setting_values ();
  let (mods, out, _err, exit_code) = parse_args ["--config"] in
  assert_equal [] mods ~pp_diff:print_mod_diff;
  assert_bool "Need config" (String.starts_with out ~prefix:"-------------------- tlapm configuration --------------------");
  (* err probably has output due to being unable to find tools; ignore *)
  assert_equal (Some 0) exit_code;
  assert_equal [] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_summary _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--summary"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("summary", summary, true); `B ("suppress_all", suppress_all, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  assert_equal false !check;
  reset_setting_values ();;

let test_timing _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--timing"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("stats", stats, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_search_paths _test_ctxt : unit =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["-I"; "some/module/path"; "-I"; "some/other/module/path"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  match changed_setting_values () with
  | [`SL ("rev_search_path", _, [_; first_path; second_path])] ->
      assert_bool "Should have first path" (string_contains "some/other/module/path" first_path);
      assert_bool "Should have second path" (string_contains "some/module/path" second_path);
  | _ -> assert_bool "Search path not as expected" false; 
  reset_setting_values ();;

let test_keep_going _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["-k"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("keep_going", keep_going, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_suppress_all _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["-N"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("suppress_all", suppress_all, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_use_isabelle_tla _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["-C"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("check", check, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_set_max_threads _test_ctxt =
  reset_setting_values ();
  let thread_count = !max_threads + 1 in
  let (mods, out, err, exit_code) = parse_args ["--threads"; Int.to_string thread_count; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`I ("max_threads", max_threads, thread_count)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_set_method _text_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--method"; "fail"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`ML ("default_method", default_method, [Tlapm_lib__Method.Fail])] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

(*
let test_set_solver _test_ctxt =
  reset_setting_values ();
  let solver_cmd = "my_solver_cmd" in
  let (mods, out, err, exit_code) = parse_args ["--solver"; solver_cmd; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  (* Params.exec is unfortunately an opaque type whose value we cannot directly access *)
  assert_bool "Solver command should be custom" (string_contains solver_cmd (solve_cmd smt "file.tla"));
  reset_setting_values ();;
*)

let test_set_smt_logic _test_ctxt =
  reset_setting_values ();
  let expected_smt_logic = "my_smt_logic" in
  let (mods, out, err, exit_code) = parse_args ["--smt-logic"; expected_smt_logic; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`S ("smt_logic", smt_logic, expected_smt_logic)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_stretch _test_ctxt =
  reset_setting_values ();
  let expected_stretch = Float.add !timeout_stretch 1.0 in
  let (mods, out, err, exit_code) = parse_args ["--stretch"; Float.to_string expected_stretch; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`F ("timeout_stretch", timeout_stretch, expected_stretch)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_no_flatten _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--noflatten"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("ob_flatten", ob_flatten, false)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_no_normalize _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--nonormal"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("pr_normal", pr_normal, false)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_debug_flags _test_ctxt =
  reset_setting_values ();
  let expected_debug_flags = ["foo"; "bar"; "baz"] in
  let (mods, out, err, exit_code) = parse_args ["--debug"; String.concat "," expected_debug_flags; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  List.iter (fun flag -> assert_bool flag (debugging flag)) expected_debug_flags;
  List.iter rm_debug_flag expected_debug_flags;
  reset_setting_values ();;

let test_toolbox_mode _test_ctxt =
  reset_setting_values ();
  let (tb_start, tb_end) = (1, 2) in
  let (mods, out, err, exit_code) = parse_args ["--toolbox"; Int.to_string tb_start; Int.to_string tb_end; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_bool "Expect toolbox output" (out <> "");
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("toolbox", toolbox, true); `I ("tb_sl", tb_sl, tb_start); `I ("tb_el", tb_el, tb_end)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_toolbox_protocol_version _test_ctxt =
  reset_setting_values ();
  let expected_toolbox_version = 3 in
  let (mods, out, err, exit_code) = parse_args ["--toolbox-vsn"; Int.to_string expected_toolbox_version; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_bool "Expect toolbox output" (out <> "");
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("toolbox", toolbox, true); `I ("toolbox_vsn", toolbox_vsn, expected_toolbox_version)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_line _test_ctxt =
  reset_setting_values ();
  let expected_line = 10 in
  let (mods, out, err, exit_code) = parse_args ["--line"; Int.to_string expected_line; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_bool "Expect toolbox output" (out <> "");
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("toolbox", toolbox, true); `I ("tb_sl", tb_sl, expected_line); `I ("tb_el", tb_el, expected_line)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_wait _test_ctxt =
  reset_setting_values ();
  let expected_wait = 30 in
  let (mods, out, err, exit_code) = parse_args ["--wait"; Int.to_string expected_wait; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`I ("wait", wait, expected_wait)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_use_stdin _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--stdin"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("use_stdin", use_stdin, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_prefer_stdlib _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--prefer-stdlib"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("prefer_stdlib", prefer_stdlib, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_no_prove _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--noproving"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("noproving", noproving, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_print_all_obligations _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--printallobs"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("printallobs", printallobs, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_safe_fingerprints _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--safefp"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("safefp", safefp, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_no_fingerprints _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--nofp"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("no_fp", no_fp, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_no_fingerprints_between_lines _test_ctxt =
  reset_setting_values ();
  let (expected_start, expected_end) = (10, 20) in
  let (mods, out, err, exit_code) = parse_args ["--nofpl"; Int.to_string expected_start; Int.to_string expected_end; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`I ("nofp_sl", nofp_sl, expected_start); `I ("nofp_el", nofp_el, expected_end)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_clean_fingerprints _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--cleanfp"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("cleanfp", cleanfp, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

(* Cannot test --erasefp due to side-effects *)
(* Cannot test --printfp due to side-effects *)

let test_use_fingerprints _test_ctxt =
  reset_setting_values ();
  let expected_fp_file = "FingerprintFile.txt" in
  let (mods, out, err, exit_code) = parse_args ["--usefp"; expected_fp_file; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`SO ("fpf_in", fpf_in, Some expected_fp_file)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_fp_deb _test_ctxt =
  reset_setting_values ();
  let (mods, out, err, exit_code) = parse_args ["--fpp"; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`B ("fp_deb", fp_deb, true)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;

let test_cache_dir _test_ctxt =
  reset_setting_values ();
  let expected_cache_dir = "some/cache/dir" in
  let (mods, out, err, exit_code) = parse_args ["--cache-dir"; expected_cache_dir; "Test.tla"] in
  assert_equal ["Test.tla"] mods ~pp_diff:print_mod_diff;
  assert_equal "" out ~pp_diff:print_string_diff;
  assert_equal "" err ~pp_diff:print_string_diff;
  assert_equal None exit_code;
  assert_equal [`S ("cachedir", cachedir, expected_cache_dir)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;
  reset_setting_values ();;
  
let cli_test_suite = "Test CLI Parsing" >::: [
  "Help Test" >:: test_help;
  "Basic Test" >:: test_basic;
  "Version Test" >:: test_version;
  "No Mods Test" >:: test_no_mods;
  "Verbose Test" >:: test_verbose;
  "Print Stlib Location Test" >:: test_where;
  "Print Config Test" >:: test_config;
  "Print Summary Test" >:: test_summary;
  "Print Stats Test" >:: test_timing;
  "Search Paths Test" >:: test_search_paths;
  "Keep Going Test" >:: test_keep_going;
  "Suppress All Test" >:: test_suppress_all;
  "Isabelle/TLA+ Check Test" >:: test_use_isabelle_tla;
  "Max Threads Test" >:: test_set_max_threads;
  "Set Method Test" >:: test_set_method;
  (*"Custom Solver Test" >:: test_set_solver;*)
  "Custom SMT Logic Test" >:: test_set_smt_logic;
  "Stretch Test" >:: test_stretch;
  "No Flatten Test" >:: test_no_flatten;
  "No Normalize Test" >:: test_no_normalize;
  "Debug Flag Test" >:: test_debug_flags;
  "Toolbox Mode Test" >:: test_toolbox_mode;
  "Toolbox Protocol Version Test" >:: test_toolbox_protocol_version;
  "Check Specific Line Test" >:: test_line;
  "Wait Before Printing Obligations Test" >:: test_wait;
  "Use Stdin Test" >:: test_use_stdin;
  "Prefer Stdlib Test" >:: test_prefer_stdlib;
  "Skip Proving Test" >:: test_no_prove;
  "Print All Obligations Test" >:: test_print_all_obligations;
  "Safe Fingerprint Check Test" >:: test_safe_fingerprints;
  "No Fingerprints Test" >:: test_no_fingerprints;
  "No Fingerprints Between Specific Lines Test" >:: test_no_fingerprints_between_lines;
  "Clean Fingerprints Test" >:: test_clean_fingerprints;
  "Use Specififc Fingerprint File Test" >:: test_use_fingerprints;
  "Test Print Fingerprints in Toolbox Messages" >:: test_fp_deb;
  "Cache Dir Test" >:: test_cache_dir;
];;

let () = run_test_tt_main cli_test_suite
