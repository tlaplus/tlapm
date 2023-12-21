(*
 * params.ml --- parameters
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)
open Ext
open Printf


let self_sum = Digest.file Sys.executable_name

(* must be a function because it must not be computed before all the
   modules are loaded. *)
let rawversion () =
  match Build_info.V1.version () with
   | None -> "development"
   | Some v -> Build_info.V1.Version.to_string v


let debug_flags : (string, unit) Hashtbl.t = Hashtbl.create 3
let add_debug_flag flg = Hashtbl.add debug_flags flg ()
let rm_debug_flag flg = Hashtbl.remove debug_flags flg
let debugging flg = Hashtbl.mem debug_flags flg

let nprocs = Sysconf.nprocs ()

let timeout_stretch = ref 1.0

let tb_sl = ref 0 (* toolbox start line *)
let tb_el = ref max_int (* toolbox end line *)
let input_files = ref []  (* List of input file names *)

let toolbox = ref false     (* Run in toolbox mode. *)

let no_fp = ref false
(* Don't use the fingerprints but still save them with the old ones. *)

let nofp_sl = ref 0
let nofp_el = ref 0
(* Don't use the fingerprints for obligations located
   between [nofp_sl] and [nofp_el] *)

let cleanfp = ref false (* Erase the fingerprint file. *)

let safefp = ref false
(* Check pm, zenon and isabelle versions before using fingerprints. *)

let wait = ref 3
(* Wait time before sending a "being proved" message to the toolbox. *)

let noproving = ref false (* Don't send any obligation to the back-ends. *)

let printallobs = ref false
(* print unnormalized and normalized versions of obligations in toolbox mode *)

(* The default library path. The relative paths (-I +some) are based on this. *)
let library_path =
  let d = Sys.executable_name in
  let d = Filename.dirname (Filename.dirname d) in
  let d = Filename.concat d "lib" in
  let d = Filename.concat d "tlaps" in
  d

let isabelle_tla_path =
    let d = Sys.executable_name in
    let d = Filename.dirname (Filename.dirname d) in
    let d = Filename.concat d "lib" in
    let d = Filename.concat d "isabelle_tla" in
    d

type executable =
  | Unchecked of string * string * string (* exec, command, version_command *)
  | User of string                        (* command *)
  | Checked of string * string list       (* command, version *)
  | NotFound of string


type exec = executable ref

(* If the backends site is not available ([]), then look for executables in the PATH,
   otherwise we are in the dune-based build and should look for the backends in the
   specified site locations. *)
let path =
  match Setup_paths.Sites.backends with
  | [] ->
    let mydir = Filename.dirname Sys.executable_name in
    let auxdir = Filename.concat library_path "bin" in
    let extrapath = sprintf ":%s:%s" mydir auxdir in
    let path = Sys.getenv "PATH" in
      sprintf "%s%s" path extrapath
  | backends_site ->
    let site_bin bs = Filename.concat bs "bin" in
    let site_isa bs = Filename.concat (Filename.concat bs "Isabelle") "bin" in
    let site_paths bs = [site_bin bs; site_isa bs] in
    let path_elems = List.concat (List.map site_paths backends_site) in
      sprintf "%s:%s" (String.concat ":" path_elems) (Sys.getenv "PATH")

let path_prefix =
  sprintf "PATH='%s';" path

let get_exec e =
  match !e with
  | Unchecked (exec, cmd, vers) ->
    (*
    let tod = Unix.gettimeofday () |> int_of_float in
    let r = 10000 + (Random.int 10000) in
     let stat = sprintf "echo path prefix: \"%s\" ; %s stat `which %s` >/tmp/stat-%d-%d.txt"
                path_prefix path_prefix exec tod r in

     ignore (Sys.command stat);
     let check = sprintf "%s type %s >/tmp/check-%d-%d.txt" path_prefix exec tod r in
       *)
     let check = sprintf "%s type %s >/dev/null" path_prefix exec in
     (* eprintf "probing command: %s\n" check; *)
     begin match Sys.command check with
     | 0 ->
        let p = Unix.open_process_in (path_prefix ^ vers) in
        let v = Std.input_list p in
        let c = sprintf "%s %s" path_prefix cmd in
        e := Checked (c, v);
        c
     | _ ->
        let msg1 = sprintf "Executable %S not found" exec in
        let msg2 =
          if Filename.is_relative exec
          then sprintf " in this PATH:\n%s\n" path
          else "."
        in
        let msg = msg1 ^ msg2 in
        eprintf "%s" msg;
        e := NotFound msg;
        failwith msg;
     end;
  | User (cmd) ->
     e := Checked (cmd, []);
     cmd
  | Checked (cmd, vers) -> cmd
  | NotFound msg -> failwith msg


let get_version e =
  match !e with
  | Checked (cmd, vers) -> vers
  | _ -> []


let make_exec cmd args version = ref (Unchecked (cmd, args, version))

let isabelle_success_string = "((TLAPS SUCCESS))"

let isabelle =
  let cmd =
    Printf.sprintf "isabelle process -e \"(use_thy \\\"$file\\\"; \
                        writeln \\\"%s\\\");\" -d %s -l TLA+"
                   isabelle_success_string
                   isabelle_tla_path
  in
  make_exec "isabelle process" cmd "isabelle version"
;;

let set_fast_isabelle () =
  if Sys.os_type <> "Cygwin" then
    eprintf "Warning: --fast-isabelle is not available on this architecture \
             (ignored)\n%!"
  else begin try
    let echos =
      "echo \"$ISABELLE_HOME\"; echo \"$ML_HOME\"; echo \"$ISABELLE_OUTPUT\""
    in
    let pr_cmd =
      sprintf "%s isabelle env sh -c %s" path_prefix (Filename.quote echos)
    in
    let ic = Unix.open_process_in pr_cmd in
    let isabelle_home = input_line ic in
    let ml_home = input_line ic in
    let isabelle_output = input_line ic in
    close_in ic;
    let poly = Filename.concat ml_home "poly" in
    let cmd =
      Printf.sprintf "export ISABELLE_HOME='%s'; \
                      export ML_HOME='%s'; \
                      (echo 'PolyML.SaveState.loadState \"%s/TLA+\"; \
                             (use_thy \"'\"$file\"'\"; writeln \"%s\");') | \
                      %s"
                     isabelle_home ml_home
                     isabelle_output isabelle_success_string poly
    in
    isabelle := Unchecked (poly, cmd, "isabelle version");
  with _ -> eprintf "Warning: error trying to set up fast-isabelle\n%!";
  end


let zenon =
  make_exec "zenon" "zenon -p0 -x tla -oisar -max-time 1d \"$file\"" "zenon -v"


let cvc4 =
  if Sys.os_type = "Cygwin" then
    make_exec "cvc4" "cvc4 --lang=smt2 \"$winfile\"" "cvc4 --version"
  else
    make_exec "cvc4" "cvc4 --lang=smt2 \"$file\"" "cvc4 --version"


let yices = make_exec "yices" "yices -tc \"$file\"" "yices --version"
let z3 =
  if Sys.os_type = "Cygwin" then
    make_exec "z3"
              (* "z3 /smt2 /v:0 AUTO_CONFIG=false PULL_NESTED_QUANTIFIERS=true MBQI=true CNF_MODE=1 PI_BLOCK_LOOOP_PATTERNS=false `cygpath -w \"$file\"`" *)  (** MBQI_MAX_ITERATIONS=10 *)
              "z3 -smt2 -v:0 AUTO_CONFIG=false smt.MBQI=true \"$winfile\""
              "z3 -version"
  else
    make_exec "z3"
              (* "z3 -smt2 -v:0 AUTO_CONFIG=false PULL_NESTED_QUANTIFIERS=true MBQI=true CNF_MODE=1 \"$file\"" *)
              "z3 -smt2 -v:0 AUTO_CONFIG=false smt.MBQI=true \"$file\""
              "z3 -version"

let verit =
  make_exec "veriT"
            "veriT --input=smtlib2 --disable-ackermann \
                   --disable-banner --disable-print-success \"$file\""
            "echo unknown"


let spass_dfg =
  make_exec "SPASS"
            "SPASS -Auto -PGiven=0 -PProblem=0 -PStatistic=0 \"$file\""
            "echo unknown"
let spass_tptp =
  make_exec "SPASS"
            "SPASS -Auto -TPTP -PGiven=0 -PProblem=0 -PStatistic=0 \"$file\""
            "echo unknown"


let eprover =
  make_exec "eprover"
            "eprover --auto --tstp-format --silent \"$file\""
            "eprover --version"


let ls4 =
  make_exec "ls4"
            "ptl_to_trp -i $file | ls4"
            "echo unknown"


let smt_logic = ref "UFNIA"

(* The default SMT solver is now Z3. The user can override it with:
   - environment variable TLAPM_SMT_SOLVER
   - command-line option --solver
   - explicit directive in the BY statement
*)
let smt =
  try ref (User (Sys.getenv "TLAPM_SMT_SOLVER"))
  with Not_found -> ref !z3
    (* "verit --input=smtlib2 --disable-ackermann --disable-banner $file" *)
    (* "z3 /smt2 MODEL=true PULL_NESTED_QUANTIFIERS=true $file" *)
    (* Yices does not handle SMTLIB version 2 yet *)

let set_smt_solver slv = smt := User slv

let set_smt_logic logic = smt_logic := logic


let max_threads = ref nprocs

(* The actual list of paths at which the library TLA files are searched. *)
let rev_search_path = ref (library_path :: Setup_paths.Sites.stdlib)

(* Additional paths are added to the search list by keeping the base path as the first one. *)
let add_search_dir dir =
  let dir =
    if dir.[0] = '+'
    then Filename.concat library_path (String.sub dir 1 (String.length dir - 1))
    else dir
  in
  if List.for_all (fun lp -> lp <> dir) !rev_search_path then
    rev_search_path := library_path :: dir :: List.tl !rev_search_path

let output_dir = ref "."

let default_method =
  ref [
    Method.Smt3 Method.default_smt2_timeout;
    Method.Zenon Method.default_zenon_timeout;
    Method.Isabelle (Method.default_isabelle_timeout,
                     Method.default_isabelle_tactic);
  ]


let mk_meth name timeout =
  match name with
  | "zenon" ->
     let timeout = Option.default Method.default_zenon_timeout timeout in
     Method.Zenon timeout
  | "auto" | "blast" | "force" ->
     let timeout = Option.default Method.default_isabelle_timeout timeout in
     Method.Isabelle (timeout, name)
  | "smt" ->
     let timeout = Option.default Method.default_smt2_timeout timeout in
     Method.Smt3 timeout
  | "z3" ->
     let timeout = Option.default Method.default_smt2_timeout timeout in
     Method.Z33 timeout
  | "cvc4" ->
     let timeout = Option.default Method.default_smt2_timeout timeout in
     Method.Cvc33 timeout
  | "yices" ->
     let timeout = Option.default Method.default_smt2_timeout timeout in
     Method.Yices3 timeout
  | "verit" ->
     let timeout = Option.default Method.default_smt2_timeout timeout in
     Method.Verit timeout
  | "spass" ->
     let timeout = Option.default Method.default_spass_timeout timeout in
     Method.Spass timeout
  | "tptp" ->
     let timeout = Option.default Method.default_tptp_timeout timeout in
     Method.Tptp timeout
  | "ls4" ->
     let timeout = Option.default Method.default_ls4_timeout timeout in
     Method.LS4 timeout
  | "fail" -> Method.Fail
  | _ -> failwith (sprintf "unknown method %S" name)


(** Raise Failure in case of syntax error or unknown method. *)
let parse_default_methods s =
  if s = "help" then begin
    printf "configured methods:\n\n" ;
    printf "  zenon   -- Zenon\n";
    printf "  auto    -- Isabelle with \"auto\" tactic\n";
    printf "  blast   -- Isabelle with \"blast\" tactic\n";
    printf "  force   -- Isabelle with \"force\" tactic\n";
    printf "  smt     -- Default SMT solver\n";
    printf "  z3      -- Z3\n";
    printf "  cvc4    -- CVC4\n";
    printf "  yices   -- Yices\n";
    printf "  verit   -- VeriT\n";
    printf "  spass   -- SPASS\n";
    printf "  ls4     -- LS4\n";
    printf "\n" ;
    printf "  fail    -- Dummy method that always fails\n" ;
    exit 0
  end else begin
    let f x =
      if String.contains x ':' then
        try
          Scanf.sscanf x "%[^:]:%f" (fun name time -> mk_meth name (Some time))
        with Scanf.Scan_failure _ ->
          failwith "bad timeout specification: not a number"
      else
        mk_meth x None
    in
    List.map f (Ext.split s ',')
  end


let set_default_method meths =
  default_method := parse_default_methods meths


let verbose = ref false

let ob_flatten = ref true
let () =
  try match Sys.getenv "TLAPM_FLATTEN" with
    | "yes" | "true" -> ob_flatten := true
    | _ -> ob_flatten := false
  with Not_found -> ()

let pr_normal = ref true
let () =
  try match Sys.getenv "TLAPM_NORMALIZE" with
    | "yes" | "true" -> pr_normal := true
    | _ -> pr_normal := false
  with Not_found -> ()

let notl     = ref false
let xtla     = ref false
let use_xtla = ref false
let () =
  try match Sys.getenv "TLAPM_CACHE" with
    | "gen" ->
        xtla := true ;
        use_xtla := false
    | "use" ->
         xtla := true ;
        use_xtla:= true
    | _ ->
        xtla := false ;
        use_xtla := false
  with Not_found -> ()

(* The `cachedir` is where `tlapm`
stores fingerprint and auxiliary
files. This directory can be defined:
- via the environment variable
  that is read below, or
- via the command-line option
  `--cache-dir`
*)
let cachedir = ref ""
let () =
    try
        cachedir := Sys.getenv "TLAPM_CACHE_DIR";
    with Not_found ->
        cachedir := ".tlacache"
let set_tlapm_cache_dir dir = cachedir := dir


let keep_going   = ref false
let suppress_all = ref false
let check        = ref false
let summary      = ref false
let stats        = ref false

let solve_cmd cmd file =
  if Sys.os_type = "Cygwin" then
    sprintf "file=%s; winfile=\"`cygpath -a -w \"%s\"`\"; %s" file file (get_exec cmd)
  else
    sprintf "file=%s; %s" file (get_exec cmd)


let external_tool_config force (name, tool) =
  if force then begin
    try ignore (get_exec tool) with Failure _ -> ()
  end;
  match !tool with
  | Checked (cmd, []) ->
      [sprintf "%s == %S" name cmd]
  | Checked (cmd, v::_) ->
      [sprintf "%s == %S" name cmd;
       sprintf "%s version == %S" name v]
  | NotFound msg ->
      [msg]
  | _ -> []


let configuration toolbox force =
  let lines =
    [ "version == \"" ^ rawversion () ^ "\""
    ; "built_with == \"OCaml " ^ Sys.ocaml_version ^ "\""
    ; "tlapm_executable == \"" ^ Sys.executable_name ^ "\""
    ; "max_threads == " ^ string_of_int !max_threads
    ; "library_path == \"" ^ String.escaped library_path ^ "\"" ]
    @ begin match !rev_search_path with
      | [] -> ["search_path == << >>"]
      | [p] -> ["search_path == << \"" ^ p ^ "\" >>"]
      | last :: sp -> begin
          let sp = List.rev sp in
          let first_line = "search_path == << \"" ^ List.hd sp ^ "\"" in
          let mid_lines = List.map begin
            fun l -> "                , \"" ^ l ^ "\""
          end (List.tl sp) in
          let last_line = "                , \"" ^ last ^ "\" >>" in
          first_line :: mid_lines @ [last_line]
        end
      end
    @ List.flatten (List.map (external_tool_config force)
                             [("Isabelle", isabelle);
                              ("zenon", zenon);
                              ("CVC4", cvc4);
                              ("Yices", yices);
                              ("Z3", z3);
                              ("VeriT", verit);
                              ("SMT", smt);
                              ("Spass", spass_tptp);
                              ("LS4", ls4);
                             ])
    @ [ "flatten_obligations == " ^ (if !ob_flatten then "TRUE" else "FALSE")
      ; "normalize == " ^ (if !pr_normal then "TRUE" else "FALSE") ]
  in
  let (header, footer) =
    if toolbox then ([], []) else
      let h = "-------------------- tlapm configuration --------------------" in
      ([h], [String.make (String.length h) '='])
  in
  header @ lines @ footer


let printconfig force =
  String.concat "\n" (configuration false force)

let print_config_toolbox force =
  String.concat "\n" (configuration true force)


let zenon_version = ref None

let check_zenon_ver () =
  let zen = get_exec zenon in
  match get_version zenon with
  | [] -> ()
  | ret :: _ ->
     Scanf.sscanf ret
       "zenon version %d.%d.%d [%c%d] %4d-%02d-%02d"
       (fun _ _ _ _ znum year month date ->
          zenon_version := Some (zen, znum, year * 10000 + month * 100 + date))


let get_zenon_verfp () = if !zenon_version = None then check_zenon_ver ();
  "Zenon version ["^(string_of_int (let _,znum,_ = Option.get !zenon_version in znum))^"]"

let isabelle_version = ref None

let check_isabelle_ver () =
  (try ignore (get_exec isabelle) with Failure _ -> ());
  match get_version isabelle with
  | [] -> ()
  | ret :: _ ->
     isabelle_version := Some (List.hd (Ext.split ret ':'))

let get_isabelle_version () =
  if !isabelle_version = None then check_isabelle_ver ();
  match !isabelle_version with
  | None -> "(unknown)"
  | Some s -> s


let fpf_out: string option ref = ref None

let fpf_in: string option ref = ref None

let fp_loaded = ref false

let fp_original_number = ref (-1)

let fp_hist_dir = ref ""

let fp_deb = ref false

let backend_timeout = ref 5.
(** How much time a back-end is allowed to spend processing the obligation
   before sending it to its external prover. This gets multiplied by
   timeout_stretch before use.
*)
