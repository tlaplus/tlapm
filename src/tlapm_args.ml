(*
 * tlapm_args.ml --- arguments for tlapm
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

open Ext
open Params

let show_config = ref false
let show_version () =
  print_endline (rawversion ()) ;
  exit 0

let set_debug_flags flgs =
  let flgs = Ext.split flgs ',' in
  let f flg =
    match flg.[0] with
    | '-' -> rm_debug_flag (String.sub flg 1 (String.length flg - 1))
    | _ -> add_debug_flag flg
  in
  List.iter f flgs
;;

let set_max_threads n =
  if n < 0 then raise (Arg.Bad "--threads requires a positive argument") ;
  max_threads := n

let set_target_start s =
  toolbox := true;
  tb_sl := s

let set_target_end e =
  tb_el := if e = 0 then max_int else e

let set_default_method meth =
  try set_default_method meth
  with Failure msg -> raise (Arg.Bad ("--method: " ^ msg))
;;

(* FIXME use Arg.parse instead *)
let parse_args args opts mods usage_fmt =
  try
    Arg.parse_argv (Array.of_list args) opts (fun mfile -> mods := mfile :: !mods)
      (Printf.sprintf usage_fmt (Filename.basename Sys.executable_name))
  with Arg.Bad msg ->
    print_endline msg ;
    flush stdout ;
    exit 2

let show_where () =
  Printf.printf "%s\n" library_path ;
  exit 0

let set_nofp_start s =
  nofp_sl := s

let set_nofp_end e =
  nofp_el := e


let print_fp fic =
  Backend.Fpfile.print fic;
  exit 0;
;;

let use_fp fic =
  fpf_in := Some fic

let erase_fp_file = ref ""
let set_erase_fp_file fic = erase_fp_file := fic

(* FIXME this should share the parsing code with --method
   or maybe just remove this option... *)
let erase_fp backend =
  let fic = !erase_fp_file in
  if (not (Sys.file_exists fic)) then begin
    raise (Arg.Bad (Printf.sprintf "File %s does not exist." fic));
  end;
  begin match backend with
  | "zenon" ->
     let m = Method.Zenon 0. in
     Backend.Fpfile.erase_results fic m;
  | "isabelle" ->
     let m = Method.Isabelle (0., "") in
     Backend.Fpfile.erase_results fic m;
  | "cooper" -> Backend.Fpfile.erase_results fic Method.Cooper;
  | _ ->
     let msg = "Valid arguments for --erasefp are {zenon,isabelle,cooper}" in
     raise (Arg.Bad msg);
  end;
  exit 0;
;;

let deprecated flag nargs =
  let f _ = Printf.eprintf "Warning: %s is deprecated (ignored)\n%!" flag in
  match nargs with
  | 0 -> flag, Arg.Unit f, ""
  | 1 -> flag, Arg.String f, ""
  | _ ->
     let args = Array.to_list (Array.make nargs (Arg.String f)) in
     flag, Arg.Tuple args, ""
;;

let quote_if_needed s =
  let check c =
    match c with
    | '+' | ',' | '-' | '.' | '/' | '0'..'9' | ':' | '=' | '@' | 'A'..'Z'
      | '_' | 'a'..'z' -> ()
    | _ -> raise Exit
  in
  if s = "" then Filename.quote s else begin
    try String.iter check s; s
    with Exit -> Filename.quote s
  end
;;

let init () =
  let mods = ref [] in
  let helpfn = ref (fun () -> ()) in
  let show_help () = !helpfn () in
  let sep = Arg.Unit show_help in
  let blank = "", sep, " " in
  let title s = s, sep, " " in
  let opts = [
    blank;
    title "(basic options)";
    blank;
    "--help", Arg.Unit show_help, " show this help message and exit" ;
    "-help", Arg.Unit show_help, " (same as --help)" ;
    "--version", Arg.Unit show_version, " show version number and exit" ;
    "--verbose", Arg.Set verbose, " produce verbose messages" ;
    "-v", Arg.Set verbose, " (same as --verbose)" ;
    blank;
    "--where", Arg.Unit show_where,
               " show location of standard library and exit" ;
    "--config", Arg.Set show_config, " show configuration and exit" ;
    "--summary", Arg.Set summary,
                 " show summary of theorems (implies -N and not -C)" ;
    "--timing", Arg.Set stats, " show runtime statistics" ;
    blank;
    "-I", Arg.String add_search_dir, "<dir> add <dir> to search path" ;
    deprecated "-d" 1;
    blank;
    "-k", Arg.Set keep_going, " keep going on backend failures" ;
    "-N", Arg.Set suppress_all, " do not run any backend verifiers" ;
    "-C", Arg.Set check, " check proofs in Isabelle/TLA+" ;
    blank;
    "--threads", Arg.Int set_max_threads,
                 "<int> set number of worker threads to <int>" ;
    "--method", Arg.String set_default_method,
                "<meth> set default method to <meth> (try --method help)" ;
    "--solver", Arg.String set_smt_solver,
                "<solver> set SMT solver to <solver>";
    "--fast-isabelle", Arg.Unit Params.set_fast_isabelle,
                       " (Windows-only) Launch Isabelle with fast shortcut";
    "--stretch", Arg.Set_float Params.timeout_stretch,
              "<f> multiply all timeouts by <f>";
    blank;
    title "(advanced options)" ;
    blank;
    "--noflatten", Arg.Clear ob_flatten, " do not flatten obligations" ;
    "--nonormal", Arg.Clear pr_normal,
                  " do not normalize obligations before printing" ;
    "--debug", Arg.String set_debug_flags,
               "{[-]<flag>} enable/disable debugging flags" ;
               (* NOTE Available flags are (non-exhaustive list):
                 * "verbose"    display message between encoding steps
                 * "noarith"    don't use the primitive sort int of SMT-LIB (entails t0)
                 * "t0"         set type level on 0
                 * "t0+"        like t0 but allow int (default)
                 * "t1"         set type level on 1
                 * "oldsmt"     use the old version of SMT (default)
                 * "newsmt"     use the new version of SMT
                 * "(no)effaxms"
                 *              use efficient axioms (more patterns)
                 * "(no)efffcns"
                 *              use efficient axioms for functions
                 * (no)rw       simplify expressions (rewriting)
                 * (no)smartflatten
                 *              try to reuse previous results of flattening
                 * "nonewqut"   don't apply simplifications that introduce quantifiers
                 * "rwsetext"   always rewrite equalities between sets
                 * "smt_prove_false"
                 *              replace the goal with FALSE to catch bugs
                 *)
    deprecated "--paranoid" 0;
    deprecated "--isaprove" 0;
    blank;
    "--toolbox", (Arg.Tuple [Arg.Int set_target_start;Arg.Int set_target_end]),
                 "<int><int> toolbox mode";
    "--wait", Arg.Set_int wait,
              "<time> wait for <time> before printing obligations in progress";
    "--noproving", Arg.Set noproving,
                   " do not prove, report fingerprinted results only";
    blank;
    "--printallobs", Arg.Set printallobs,
                     " print obligations in all toolbox messages";
    blank;
    deprecated "--fpdir" 1;
    "--safefp", Arg.Set Params.safefp,
                " check tlapm, zenon, Isabelle versions for fingerprints";
    "--nofp", Arg.Set Params.no_fp, " disable fingerprint use";
    "--nofpl", (Arg.Tuple [Arg.Int set_nofp_start;Arg.Int set_nofp_end]),
               "<int><int> disable fingerprint use between given lines";
    "--cleanfp", Arg.Set Params.cleanfp,
                 " erase fingerprint file before starting";
    blank;
    "--erasefp", (Arg.Tuple [Arg.String set_erase_fp_file;Arg.String erase_fp]),
                 "<f><back> erase from file <f> all results of backend <back>";
    "--printfp", Arg.String print_fp,
                 "<f> print the fingerprints stored in file <f> and quit";
    "--usefp", Arg.String use_fp,
               "<f> load fingerprints from file <f> (save as usual)";
    "--fpp", Arg.Set fp_deb,
             " print the fingerprints of obligations in toolbox messages";
  ]
  in
  let opts = Arg.align opts in
  let usage_fmt =
    format_of_string "Usage: %s <options> FILE ...\noptions are:"
  in
  helpfn := begin fun () ->
    Arg.usage opts
      (Printf.sprintf usage_fmt (Filename.basename Sys.executable_name)) ;
    exit 0
  end ;
  let args = Array.to_list Sys.argv in
  parse_args args opts mods usage_fmt ;
  if !show_config || !verbose then begin
    print_endline (printconfig true) ;
    flush stdout
  end ;
  if !show_config then exit 0 ;
  if !mods = [] then begin
    Arg.usage opts
      (Printf.sprintf "Need at least one module file.\n\n\
                       Usage: %s <options> FILE ...\noptions are:"
         (Filename.basename Sys.executable_name)) ;
    exit 2
  end ;
  if !summary then begin
    suppress_all := true ;
    check := false ;
  end ;
  check_zenon_ver () ;
  if !Params.toolbox then begin
    Printf.printf "\n\\* TLAPM version %d.%d.%d (commit %s)\n"
                  Version.major Version.minor Version.micro (Revision.get ());
    let tm = Unix.localtime (Unix.gettimeofday ()) in
    Printf.printf "\\* launched at %04d-%02d-%02d %02d:%02d:%02d"
                  (tm.Unix.tm_year + 1900) (tm.Unix.tm_mon + 1) tm.Unix.tm_mday
                  tm.Unix.tm_hour tm.Unix.tm_min tm.Unix.tm_sec;
    Printf.printf " with command line:\n\\*";
    Array.iter (fun s -> Printf.printf " %s" (quote_if_needed s)) Sys.argv;
    Printf.printf "\n\n%!"
  end;
  !mods
