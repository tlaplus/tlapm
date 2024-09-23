(* Command-line arguments to `tlapm`.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open Ext
open Params


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


let set_max_threads n =
  if n < 0 then raise (Arg.Bad "--threads requires a positive argument") ;
  max_threads := n

let set_target_start s =
  toolbox := true;
  tb_sl := s

let set_target_end e =
  tb_el := if e = 0 then max_int else e

let set_toolbox_vsn vsn =
  toolbox := true;
  toolbox_vsn := vsn

let set_target_line s =
    toolbox := true;
    if s = 0 then begin
        tb_sl := 0;
        tb_el := max_int
    end else begin
        tb_sl := s;
        tb_el := s
    end

let set_default_method meth =
  try set_default_method meth
  with Failure msg -> raise (Arg.Bad ("--method: " ^ msg))


let show_where () =
  match stdlib_path with
  | Some path  ->
    Printf.printf "%s\n" path;
    exit 0
  | None ->
    Printf.printf "N/A\n";
    exit 1

let set_nofp (s, e) =
  nofp_sl := s;
  nofp_el := e


let print_fp fic =
  Backend.Fpfile.print fic;
  exit 0


let use_fp fic =
  fpf_in := Some fic

(* FIXME this should share the parsing code with --method
   or maybe just remove this option... *)
let erase_fp (fic, backend) =
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
  exit 0


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


open Cmdliner

let version_t =
  let doc = "Show version number and exit." in
  Arg.(value & flag & info ["version"] ~doc)

let verbose_t =
  let doc = "Show version number and exit." in
  Arg.(value & flag & info ["v"; "verbose"] ~doc)

let where_t =
  let doc = "Show location of standard library and exit." in
  Arg.(value & flag & info ["where"] ~doc)

let config_t =
  let doc = "Show configuration and exit." in
  Arg.(value & flag & info ["config"] ~doc)

let summary_t =
  let doc = "Show summary of theorems (implies -N and not -C)." in
  Arg.(value & flag & info ["summary"] ~doc)

let timing_t =
  let doc = "Show runtime statistics." in
  Arg.(value & flag & info ["timing"] ~doc)

let search_dir_t =
  let doc = "Add $(docv) to search path." in
  Arg.(value & opt_all dir [] & info ["I"] ~docv:"DIR" ~doc)

let keep_going_t =
  let doc = "Keep going on backend failures." in
  Arg.(value & flag & info ["k"] ~doc)

let suppress_all_t =
  let doc = "Do not run any backend verifiers." in
  Arg.(value & flag & info ["N"] ~doc)

let check_t =
  let doc = "Check proofs in Isabelle/TLA+." in
  Arg.(value & flag & info ["C"] ~doc)

let threads_t =
  let doc = "Set number of worker threads to $(docv)." in
  Arg.(value & opt (some int) None & info ["threads"] ~docv:"N" ~doc)

let method_t =
  let doc = "Set default method to $(docv) (try --method=help)." in
  Arg.(value & opt (some string) None & info ["method"] ~docv:"METH" ~doc)

let solver_t =
  let doc = "Set SMT solver to $(docv)." in
  Arg.(value & opt (some string) None & info ["solver"] ~docv:"SOLVER" ~doc)

let smt_logic_t =
  let doc = "Set SMT logic to $(docv)." in
  Arg.(value & opt (some string) None & info ["smt-logic"] ~docv:"LOGIC" ~doc)

let fast_isabelle_t =
  let doc = "(Windows-only) Launch Isabelle with fast shortcut." in
  Arg.(value & flag & info ["fast-isabelle"] ~doc)

let stretch_t =
  let doc = "Multiply all timeouts by $(docv)." in
  Arg.(value & opt float 1.0 & info ["stretch"] ~docv:"MULTIPLIER" ~doc)

let noflatten_t =
  let doc = "Do not flatten obligations." in
  Arg.(value & flag & info ["noflatten"] ~doc)

let nonormal_t =
  let doc = "Do not normalize obligations before printing." in
  Arg.(value & flag & info ["nonormal"] ~doc)

let debug_t =
  let doc = "Enable/disable debugging flags." in
  Arg.(value & opt_all string [] & info ["debug"] ~docv:"[-]flag" ~doc)

let toolbox_t =
  let doc = "Toolbox mode." in
  Arg.(value & opt (some (pair int int)) None & info ["toolbox"] ~doc)

let toolbox_vsn_t =
  let doc = "Toolbox protocol version." in
  Arg.(value & opt int 1 & info ["toolbox-vsn"] ~docv:"1|2" ~doc)

let line_t =
  let doc = "Line to prove." in
  Arg.(value & opt (some int) None & info ["line"] ~docv:"LINENO" ~doc)

let wait_t =
  let doc = "Wait for $(docv) before printing obligations in progress." in
  Arg.(value & opt int 3 & info ["wait"] ~docv:"TIME" ~doc)

let stdin_t =
  let doc = "Read the tla file from stdin instead of file system. \
             Only applies if single tla file is provided as input." in
  Arg.(value & flag & info ["stdin"] ~doc)

let prefer_stdlib_t =
  let doc = "Prefer build-in standard modules if the module search path \
             contains files with the same names as modules in stdlib." in
  Arg.(value & flag & info ["prefer-stdlib"] ~doc)

let noproving_t =
  let doc = "Do not prove, report fingerprinted results only." in
  Arg.(value & flag & info ["noproving"] ~doc)

let printallobs_t =
  let doc = "Print obligations in all toolbox messages." in
  Arg.(value & flag & info ["printallobs"] ~doc)

let safefp_t =
  let doc = "Check tlapm, zenon, Isabelle versions for fingerprints." in
  Arg.(value & flag & info ["safefp"] ~doc)

let nofp_t =
  let doc = "Do not use existing fingerprints, \
             but overwrite any preexisting fingerprints associated \
             with the current proof obligations, \
             using the newly computed fingerprints and results" in
  Arg.(value & flag & info ["nofp"] ~doc)

let nofpl_t =
  let doc = "Disable fingerprint use between given lines." in
  Arg.(value & opt (some (pair int int)) None & info ["nofpl"] ~doc)

let cleanfp_t =
  let doc = "Erase fingerprint file before starting." in
  Arg.(value & flag & info ["cleanfp"] ~doc)

let erasefp_t =
  let doc = "Erase from file FILE all results of backend BACK." in
  Arg.(value & opt (some (pair file string)) None & info ["erasefp"] ~docv:"FILE,BACK" ~doc)

let printfp_t =
  let doc = "Print the fingerprints stored in file $(docv) and quit." in
  Arg.(value & opt (some file) None & info ["printfp"] ~docv:"FILE" ~doc)

let usefp_t =
  let doc = "Load fingerprints from file $(docv) (save as usual)." in
  Arg.(value & opt (some file) None & info ["usefp"] ~docv:"FILE" ~doc)

let fpp_t =
  let doc = "Print the fingerprints of obligations in toolbox messages." in
  Arg.(value & flag & info ["fpp"] ~doc)

let cache_dir_t =
  let doc = "Save auxiliary and \
             temporary files under $(docv). \
             Alternatively, this directory \
             can be defined via the variable \
             `TLAPM_CACHE_DIR` of the runtime \
             environment. The command-line \
             parameter takes precedence over \
             the environment variable. If neither \
             is specified, the default value is \".tlacache\"." in
  Arg.(value & opt (some dir) None & info ["cache-dir"] ~docv:"DIR" ~doc)

let files_t =
  let doc = "Files to process." in
  Arg.(value & pos_all string [] & info [] ~docv:"FILE" ~doc)

let final flag f () =
  if flag then (f (); `Final) else `Continue

let set value reference () =
  if value then reference := true;
  `Continue

let clear value reference () =
  if value then reference := false;
  `Continue

let setr value reference () =
  reference := value;
  `Continue

let setf value f () =
  let () =
    match value with
    | None -> ()
    | Some x -> f x
  in
  `Continue

let ( *** ) a b =
  match a () with
  | `Final -> ()
  | `Continue -> b

let main version verbose_ where config summary_ timing search_dir keep_going_
      suppress_all_ check_ threads method_ solver smt_logic fast_isabelle
      stretch noflatten nonormal debug toolbox toolbox_vsn line wait_
      stdin prefer_stdlib_ noproving_ printallobs_ safefp_ nofp nofpl cleanfp_
      erasefp printfp usefp fpp cache_dir mods =
  let () =
    final version show_version
    *** set verbose_ verbose
    *** final where show_where
    *** set summary_ summary
    *** set timing stats
    *** (fun () -> List.iter add_search_dir search_dir; `Continue)
    *** set keep_going_ keep_going
    *** set suppress_all_ suppress_all
    *** set check_ check
    *** setf threads set_max_threads
    *** setf method_ set_default_method
    *** setf solver set_smt_solver
    *** setf smt_logic set_smt_logic
    *** (fun () -> if fast_isabelle then Params.set_fast_isabelle (); `Continue)
    *** setr stretch Params.timeout_stretch
    *** clear noflatten ob_flatten
    *** clear nonormal pr_normal
    *** (fun () -> List.iter set_debug_flags debug; `Continue)
    *** setf toolbox (fun (s, e) -> set_target_start s; set_target_end e)
    *** (fun () -> set_toolbox_vsn toolbox_vsn; `Continue)
    *** setf line set_target_line
    *** setr wait_ wait
    *** set stdin use_stdin
    *** set prefer_stdlib_ prefer_stdlib
    *** set noproving_ noproving
    *** set printallobs_ printallobs
    *** set safefp_ safefp
    *** set nofp no_fp
    *** setf nofpl set_nofp
    *** set cleanfp_ cleanfp
    *** setf erasefp erase_fp
    *** setf printfp print_fp
    *** setf usefp use_fp
    *** set fpp fp_deb
    *** setf cache_dir set_tlapm_cache_dir
    *** ()
  in
  if config || !verbose then begin
    print_endline (printconfig true);
    flush stdout;
  end;
  if config then exit 0;
  if mods = [] then begin
    Printf.eprintf "Need at least one module file.\n%!";
    exit 2;
  end;
  if !summary then begin
    suppress_all := true;
    check := false;
  end;
  check_zenon_ver ();
  if !Params.toolbox then begin
    Printf.printf "\n\\* TLAPM version %s\n"
                  (Params.rawversion ());
    let tm = Unix.localtime (Unix.gettimeofday ()) in
    Printf.printf "\\* launched at %04d-%02d-%02d %02d:%02d:%02d"
                  (tm.Unix.tm_year + 1900) (tm.Unix.tm_mon + 1) tm.Unix.tm_mday
                  tm.Unix.tm_hour tm.Unix.tm_min tm.Unix.tm_sec;
    Printf.printf " with command line:\n\\*";
    Array.iter (fun s -> Printf.printf " %s" (quote_if_needed s)) Sys.argv;
    Printf.printf "\n\n%!"
  end;
  if !use_stdin && (List.length mods) <> 1 then begin
    Printf.eprintf
      "Exactly 1 module has to be specified if TLAPM is invoked with\
       the --stdin option.\n%!";
    exit 2
  end;
  mods

let term =
  Term.(const main $ version_t $ verbose_t $ where_t $ config_t $ summary_t $ timing_t
        $ search_dir_t $ keep_going_t $ suppress_all_t $ check_t $ threads_t $ method_t
        $ solver_t $ smt_logic_t $ fast_isabelle_t $ stretch_t $ noflatten_t $ nonormal_t
        $ debug_t $ toolbox_t $ toolbox_vsn_t $ line_t $ wait_t $ stdin_t $ prefer_stdlib_t
        $ noproving_t $ printallobs_t $ safefp_t $ nofp_t $ nofpl_t $ cleanfp_t
        $ erasefp_t $ printfp_t $ usefp_t $ fpp_t $ cache_dir_t $ files_t)

let cmd =
  let info = Cmd.info "tlapm" in
  Cmd.v info term

let init () =
  match Cmd.eval_value' cmd with
  | `Ok x -> x
  | `Exit r -> exit r
