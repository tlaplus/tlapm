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

open OUnit2;;
open Tlapm_lib__Tlapm_args;;

let test_basic _test_ctxt =
  reset_setting_values ();
  assert_equal ["Test.tla"] (init "tlapm" [|"tlapm"; "Test.tla";|]);
  assert_equal [] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;;

let test_verbose_short _test_ctxt =
  reset_setting_values ();
  assert_equal ["Test.tla"] (init "tlapm" [|"tlapm"; "-v"; "Test.tla";|]);
  assert_equal [`B ("verbose", verbose, false)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;;

let test_verbose_long _test_ctxt =
  reset_setting_values ();
  assert_equal ["Test.tla"] (init "tlapm" [|"tlapm"; "--verbose"; "Test.tla";|]);
  assert_equal [`B ("verbose", verbose, false)] (changed_setting_values ()) ~pp_diff:print_setting_list_diff;;

let cli_test_suite = "Test CLI Parsing" >::: [
  "Basic Test"    >:: test_basic;
  "Verbose Short" >:: test_verbose_short;
  "Verbose Long"  >:: test_verbose_long;
];;

let () = run_test_tt_main cli_test_suite
