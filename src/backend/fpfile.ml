(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(* Each version of the fingerprint file format has its own module here.
   DO NOT EVER CHANGE THE MODULES DEFINED HERE.  You must define a new
   module for each new format.
*)

open Ext;;


module V13 = struct

  (* introduced on 2019- in revision *)
  (* Adds the cases "ExpandENABLED", "ExpandCdot", "AutoUSE", "Lambdify",
     "ENABLEDaxioms", "LevelComparison"
     to type meth.
   *)

  type floatomega = F of float | Omega;;

  type meth =
  | Isabelle of isabelle
  | Zenon of zenon
  | Smt
  | SmtT of floatomega
  | Yices
  | YicesT of floatomega
  | Z3
  | Z3T of floatomega
  | Cooper
  | Sorry
  | Fail
  | Cvc3T of floatomega
  | Smt2lib of floatomega
  | Smt2z3 of floatomega
  | Smt3 of floatomega
  | Z33 of floatomega
  | Cvc33 of floatomega
  | Yices3 of floatomega
  | Verit of floatomega
  | Spass of floatomega
  | Tptp of floatomega
  | LS4 of floatomega
  | ExpandENABLED
  | AutoUSE  (* as needed for expanding `ENABLED` and `\cdot` *)
  | ExpandCdot
  | Lambdify
  | ENABLEDaxioms
  | LevelComparison
  | Trivial

  and zenon = {
    zenon_timeout : float;
    zenon_fallback : meth;
  }

  and isabelle = {
    isabelle_timeout : floatomega;
    isabelle_tactic : string;
  }
  ;;

  type reason =
  | False
  | Timeout
  | Cantwork of string
  ;;

  type status_type_aux =
  | RSucc
  | RFail of reason option
  | RInt
  ;;

  type status_type =
  | Triv
  | NTriv of status_type_aux * meth
  ;;

  type date = int * int * int * int * int * int;;
  (* year, month-1, day, hour, minute, second *)

  type sti = status_type * date * string * string * string;;
             (* status, date, pm version, zenon version, isabelle version *)

  type str = {
    tres : sti option;
    zres : sti option;
    ires : sti option;
    smtres : sti option;
    cooperres : sti option;
    yres : sti option;
    z3res : sti option;
    cvc3res : sti option;
    smt2libres : sti option;
    smt2z3res : sti option;
    smt3res : sti option;
    z33res : sti option;
    cvc33res : sti option;
    yices3res : sti option;
    veritres : sti option;
    spassres : sti option;
    tptpres : sti option;
    ls4res : sti option;
    expandenabledres : sti option;
    expandcdotres : sti option;
    lambdifyres: sti option;
    enabledaxiomsres: sti option;
    levelcomparisonres: sti option;
  };;

  type tbl = (string, str) Hashtbl.t;;
  (* The key is the MD5 converted to hex. *)

  (* File format:
     - magic number as a marshalled integer = 20101013
     - Fpver13 of tbl
     - any number of (Digest.t, sti list) pairs
  *)

  let version = 13;;

end;;

type fp =
  | FP13 of V13.tbl
  | FPunknown of unit
;;


(* Note: the above modules and types are strictly private to this
   file and their contents must not escape from this module.
   Likewise, external types must not get into the above modules.
 *)

(* ===================================================================== *)


open Printf;;
open V13;;

let fptbl = ref (Hashtbl.create 500 : V13.tbl);;

let old_magic_number = 20101013;;
let magic_number = 20210223;;

let write_fp_table oc =
  output_value oc magic_number;
  output_value oc (FP13 !fptbl);
;;

let get_date month_offset =
  let tm = Unix.localtime (Unix.gettimeofday ()) in
  (1900 + tm.Unix.tm_year, 1 + tm.Unix.tm_mon + month_offset, tm.Unix.tm_mday,
   tm.Unix.tm_hour, tm.Unix.tm_min, tm.Unix.tm_sec)
;;

let hist_dir_name = ref "";;

module FN = Filename;;

let fp_init fp_file sources =
  let histdir = fp_file ^ ".history" in
  hist_dir_name := histdir;
  let (y, m, d, hr, mi, se) = get_date 0 in
  let date = Printf.sprintf "%04d-%02d-%02d_%02d_%02d_%02d" y m d hr mi se in
  let destdir = FN.concat histdir date in

  (* Save context and "before" version of FP. *)
  let tlasources = List.map (fun x -> x ^ ".tla") sources in
  let sourcefiles = String.concat " " (List.map FN.quote tlasources) in
  ignore (Sys.command ("mkdir -p " ^ FN.quote destdir));
  ignore (Sys.command ("cp -p " ^ FN.quote fp_file ^ " " ^ sourcefiles
                       ^ " " ^ FN.quote destdir ^ " 2>/dev/null"));

  (* Remove saved stuff beyond the 10th *)
  let hist_subdirs = FN.concat (FN.quote histdir) "*" in
  ignore (Sys.command ("rm -rf `ls -1td " ^ hist_subdirs ^ "| tail -n +11`"));

  (* Open FP file for writing and output the old fingerprints. *)
  let oc = open_out_bin fp_file in
  write_fp_table oc;
  oc
;;

module T = Types;;
module M = Method;;

(* Vx means the latest version, currently V13 *)

let rec st6_to_Vx st =
  match st with
  | T.Triv -> Triv
  | T.NTriv (sta, meth) -> NTriv (sta6_to_Vx sta, meth_to_Vx meth)

and sta6_to_Vx sta =
  match sta with
  | T.RSucc -> RSucc
  | T.RFail None -> RFail None
  | T.RFail (Some r) -> RFail (Some (reason_to_Vx r))
  | T.RInt -> RInt

and reason_to_Vx r =
  match r with
  | T.False -> False
  | T.Timeout -> Timeout
  | T.Cantwork s -> Cantwork s

and meth_to_Vx m =
  match m with
  | M.Isabelle (tmo, tac) ->
     Isabelle {isabelle_timeout = floatomega_to_Vx tmo; isabelle_tactic = tac}
  | M.Zenon tmo -> Zenon {zenon_timeout = tmo; zenon_fallback = Fail}
  | M.SmtT tmo -> SmtT (floatomega_to_Vx tmo)
  | M.YicesT tmo -> YicesT (floatomega_to_Vx tmo)
  | M.Z3T tmo -> Z3T (floatomega_to_Vx tmo)
  | M.Cooper -> Cooper
  | M.Fail -> Fail
  | M.Cvc3T tmo -> Cvc3T (floatomega_to_Vx tmo)
  | M.Smt2lib tmo -> Smt2lib (floatomega_to_Vx tmo)
  | M.Smt2z3 tmo -> Smt2z3 (floatomega_to_Vx tmo)
  | M.Smt3 tmo -> Smt3 (floatomega_to_Vx tmo)
  | M.Z33 tmo -> Z33 (floatomega_to_Vx tmo)
  | M.Cvc33 tmo -> Cvc33 (floatomega_to_Vx tmo)
  | M.Yices3 tmo -> Yices3 (floatomega_to_Vx tmo)
  | M.Verit tmo -> Verit (floatomega_to_Vx tmo)
  | M.Spass tmo -> Spass (floatomega_to_Vx tmo)
  | M.Tptp tmo -> Tptp (floatomega_to_Vx tmo)
  | M.LS4 tmo -> LS4 (floatomega_to_Vx tmo)
  | M.ExpandENABLED -> ExpandENABLED
  | M.AutoUSE -> AutoUSE
  | M.ExpandCdot -> ExpandCdot
  | M.Lambdify -> Lambdify
  | M.ENABLEDaxioms -> ENABLEDaxioms
  | M.LevelComparison -> LevelComparison
  | M.Trivial -> Trivial

and floatomega_to_Vx f = F f;;

let fp_to_Vx fp = fp;;
(* V13 fingerprints are hex-encoded digests, as are external fingerprints.
   Future versions will use raw digests, hence the need for this translation
   function.
*)

let date_to_Vx d = d;;
(* V13 dates use month-1, as do external dates.  Future versions will use
   month, hence the need for this translation function. *)

type prover =
  | Pisabelle of string
  | Pzenon
  | Psmt
  | Pyices
  | Pz3
  | Pcooper
  | Psorry
  | Pfail
  | Pcvc3
  | Psmt2lib
  | Psmt2z3
  | Psmt3
  | Pz33
  | Pcvc33
  | Pyices3
  | Pverit
  | Pspass
  | Ptptp
  | Pls4
  | Pexpandenabled
  | Pautouse
  | Pexpandcdot
  | Plambdify
  | Penabledaxioms
  | Plevelcomparison
  | Ptrivial
;;

let prover_of_method m =
  match m with
  | Isabelle {isabelle_tactic = tac} -> Pisabelle tac
  | Zenon _ -> Pzenon
  | Smt | SmtT _ -> Psmt
  | Yices | YicesT _ -> Pyices
  | Z3 | Z3T _ -> Pz3
  | Cooper -> Pcooper
  | Sorry -> Psorry
  | Fail -> Pfail
  | Cvc3T _ -> Pcvc3
  | Smt2lib _ -> Psmt2lib
  | Smt2z3 _ -> Psmt2z3
  | Smt3 _ -> Psmt3
  | Z33 _ -> Pz33
  | Cvc33 _ -> Pcvc33
  | Yices3 _ -> Pyices3
  | Verit _ -> Pverit
  | Spass _ -> Pspass
  | Tptp _ -> Ptptp
  | LS4 _ -> Pls4
  | ExpandENABLED -> Pexpandenabled
  | ExpandCdot -> Pexpandcdot
  | AutoUSE -> Pautouse
  | Lambdify -> Plambdify
  | ENABLEDaxioms -> Penabledaxioms
  | LevelComparison -> Plevelcomparison
  | Trivial -> Ptrivial
;;

let normalize m =
  match m with
  | Isabelle {isabelle_timeout = Omega; isabelle_tactic = t} ->
     Isabelle {isabelle_timeout = F infinity; isabelle_tactic = t}
  | Zenon {zenon_timeout = tmo; zenon_fallback = _} ->
     Zenon {zenon_timeout = tmo; zenon_fallback = Fail}
  | Smt | SmtT (Omega) -> SmtT (F infinity)
  | Yices | YicesT (Omega) -> YicesT (F infinity)
  | Z3 | Z3T (Omega) -> Z3T (F infinity)
  | Cvc3T (Omega) -> Cvc3T (F infinity)
  | Smt2lib (Omega) -> Smt2lib (F infinity)
  | Smt2z3 (Omega) -> Smt2z3 (F infinity)
  | Smt3 (Omega) -> Smt3 (F infinity)
  | Z33 (Omega) -> Z33 (F infinity)
  | Cvc33 (Omega) -> Cvc33 (F infinity)
  | Yices3 (Omega) -> Yices3 (F infinity)
  | Verit (Omega) -> Verit (F infinity)
  | Spass (Omega) -> Spass (F infinity)
  | Tptp (Omega) -> Tptp (F infinity)
  | LS4 (Omega) -> LS4 (F infinity)
  | _ -> m
;;

let get_timeout m =
  match m with
  | Isabelle {isabelle_timeout = F t}
  | Zenon {zenon_timeout = t}
  | SmtT (F t)
  | YicesT (F t)
  | Z3T (F t)
  | Cvc3T (F t)
  | Smt2lib (F t)
  | Smt2z3 (F t)
  | Smt3 (F t)
  | Z33 (F t)
  | Cvc33 (F t)
  | Yices3 (F t)
  | Verit (F t)
  | Spass (F t)
  | Tptp (F t)
  | LS4 (F t)
  -> t
  | _ -> infinity
;;

(* Arbitrary order on the methods, and inside each method the best result
   is greater. *)
(* FIXME this is slightly broken (as was the previous code) because
   isabelle results are compared without regard for the tactic field.
   It will become easy to fix when we change to a list of results instead
   of a record.
 *)
let order st1 st2 =
  let (r1, _, _, _, _) = st1 in
  let (r2, _, _, _, _) = st2 in
  match r1, r2 with
  | Triv, Triv -> 0
  | Triv, _ -> 1
  | _, Triv -> -1
  | NTriv (r1, m1), NTriv (r2, m2)
    when prover_of_method m1 = prover_of_method m2 ->
     begin match r1, r2 with
     | RSucc, RFail _ -> 1
     | RFail _, RSucc -> -1
     | RInt, _ -> -1
     | _, RInt -> 1
     | RSucc, RSucc -> compare (get_timeout m2) (get_timeout m1)
     | RFail _, RFail _ -> compare (get_timeout m1) (get_timeout m2)
     end
  | NTriv (_, m1), NTriv (_, m2) -> compare (normalize m1) (normalize m2)
;;

let opt_to_list o =
  match o with
  | None -> []
  | Some x -> [x]
;;

let record_to_list r =
  List.flatten [
    opt_to_list r.tres;
    opt_to_list r.zres;
    opt_to_list r.ires;
    opt_to_list r.smtres;
    opt_to_list r.cooperres;
    opt_to_list r.yres;
    opt_to_list r.z3res;
    opt_to_list r.cvc3res;
    opt_to_list r.smt2libres;
    opt_to_list r.smt2z3res;
    opt_to_list r.smt3res;
    opt_to_list r.z33res;
    opt_to_list r.cvc33res;
    opt_to_list r.yices3res;
    opt_to_list r.veritres;
    opt_to_list r.spassres;
    opt_to_list r.tptpres;
    opt_to_list r.ls4res;
  ]
;;

let empty = {
  tres = None;
  zres = None;
  ires = None;
  smtres = None;
  cooperres = None;
  yres = None;
  z3res = None;
  cvc3res = None;
  smt2libres = None;
  smt2z3res = None;
  smt3res = None;
  z33res = None;
  cvc33res = None;
  yices3res = None;
  veritres = None;
  spassres = None;
  tptpres = None;
  ls4res = None;
  expandenabledres = None;
  expandcdotres = None;
  lambdifyres = None;
  enabledaxiomsres = None;
  levelcomparisonres = None;
};;

let add_to_record r st =
  let (x, _, _, _, _) = st in
  match x with
  | Triv -> {r with tres = Some st}
  | NTriv (_, Isabelle _) -> {r with ires = Some st}
  | NTriv (_, Zenon _) -> {r with zres = Some st}
  | NTriv (_, (Smt | SmtT _)) -> {r with smtres = Some st}
  | NTriv (_, (Yices | YicesT _)) -> {r with yres = Some st}
  | NTriv (_, (Z3 | Z3T _)) -> {r with z3res = Some st}
  | NTriv (_, Cooper) -> {r with cooperres = Some st}
  | NTriv (_, Cvc3T _) -> {r with cvc3res = Some st}
  | NTriv (_, Smt2lib _) -> {r with smt2libres = Some st}
  | NTriv (_, Smt2z3 _) -> {r with smt2z3res = Some st}
  | NTriv (_, Smt3 _) -> {r with smt3res = Some st}
  | NTriv (_, Z33 _) -> {r with z33res = Some st}
  | NTriv (_, Cvc33 _) -> {r with cvc33res = Some st}
  | NTriv (_, Yices3 _) -> {r with yices3res = Some st}
  | NTriv (_, Verit _) -> {r with veritres = Some st}
  | NTriv (_, Spass _) -> {r with spassres = Some st}
  | NTriv (_, Tptp _) -> {r with tptpres = Some st}
  | NTriv (_, LS4 _) -> {r with ls4res = Some st}
  | NTriv (_, ExpandENABLED) -> {r with expandenabledres = Some st}
  | NTriv (_, ExpandCdot) -> {r with expandcdotres = Some st}
  | NTriv (_, Lambdify) -> {r with lambdifyres = Some st}
  | NTriv (_, ENABLEDaxioms) -> {r with enabledaxiomsres = Some st}
  | NTriv (_, LevelComparison) -> {r with levelcomparisonres = Some st}
  | _ -> r
;;

let list_to_record l = List.fold_left add_to_record empty l;;

let add_to_table fp l1 =
  let r = try Hashtbl.find !fptbl fp with Not_found -> empty in
  let l2 = record_to_list r in
  let l = List.sort ~cmp:order (l1 @ l2) in
  Hashtbl.replace !fptbl fp (list_to_record l)
;;

let fp_writes
        (oc: out_channel)
        (fp: string)
        (results: Types.status_type6 list):
            unit =
  let fp: string = fp_to_Vx fp in
  let date = get_date (-1) in
  let zv = Params.get_zenon_verfp () in
  let iv = Params.get_isabelle_version () in
  let f (result: Types.status_type6) =
      (
          st6_to_Vx result,  (* : status_type6 *)
          date_to_Vx date,  (* = date *)
          Params.rawversion (),  (* : string = `tlapm` version *)
          zv,  (* : string = `zenon` version *)
          iv  (* : string = `isabelle` version *)
      )
    in
  let l = List.map f results in
  (* FIXME Triv results should not be sent back to server.ml, instead
     of propagating them all the way and then eliminating them here. *)
  let filt r =
    match r with
    | (Triv, _, _, _, _) -> false
    | (NTriv (_, Fail), _, _, _, _) -> false
    | _ -> true
  in
  let l = List.filter filt l in
  Marshal.to_channel oc (fp, l) [];
  flush oc;
  add_to_table fp l;
;;

let num_fingerprints_loaded = ref 0;;

let fp_close_and_consolidate file oc =
  close_out oc;
  let tmpfile = file ^ ".tmp" in
  let noc = open_out_bin tmpfile in
  write_fp_table noc;
  close_out noc;
  Sys.rename tmpfile file;
  Util.printf "(* fingerprints written in %S *)" file;
  if Hashtbl.length !fptbl < !num_fingerprints_loaded then begin
    Errors.err "The fingerprints file %s has fewer entries than its \
                previous version (stored in %s)." file !hist_dir_name;
  end;
;;

let add_v13l fp stl = add_to_table fp stl;;

let iter_tbl vnum f fps =
  Errors.err "Translating fingerprints from version %d to version %d"
             vnum version;
  Hashtbl.iter f fps;
;;

let iter_file f ic =
  try while true do
    let v = Marshal.from_channel ic in
    f v;
  done with
  | End_of_file -> ()
  | Failure _ -> ()  (* truncated object *)
;;

let translate v ic =
  match v with
  | FP13 fps -> fptbl := fps; iter_file add_v13l ic;
  | _ -> assert false
;;

let load_fingerprints_aux file =
  if Sys.file_exists file then begin
    let ic = open_in_bin file in
    let magic = Marshal.from_channel ic in
    if magic = old_magic_number then
        failwith "fingerprint file with an older magic number";
    if magic <> magic_number then failwith "corrupted fingerprint file";
    let v = Marshal.from_channel ic in
    if v >= FPunknown ()
      then Errors.fatal "fingerprint file is from a newer version of tlapm";
    translate v ic;
    close_in ic;
    if !Params.safefp then begin
      (* Erase fingerprints from other versions of Zenon and Isabelle. *)
      let oldtbl = !fptbl in
      fptbl := Hashtbl.create 500;
      let zv0 = Params.get_zenon_verfp () in
      let iv0 = Params.get_isabelle_version () in
      let keep (st, _, _, zv, iv) =
        match st with
        | NTriv (_, Zenon _) -> zv = zv0
        | NTriv (_, Isabelle _) -> iv = iv0
        | _ -> true
      in
      let process fp r =
        let l = List.filter keep (record_to_list r) in
        Hashtbl.add !fptbl fp (list_to_record l);
      in
      Hashtbl.iter process oldtbl;
    end;
  end;
;;

let previous_fp_file file =
  let histdir = file ^ ".history" in
  let cmd = sprintf "ls -td %s/*/fingerprints" (FN.quote histdir) in
  let ic = Unix.open_process_in cmd in
  let prev =
    try
        input_line ic
    with End_of_file ->
        close_in_noerr ic;
        failwith ("`ls` returned no stdout \
            when looking for older fingerprints file, \
            so it appears that there are no older fingerprints files.")
  in
  let proc_st = Unix.close_process_in ic in
  begin match proc_st with
  | WEXITED exit_code -> begin
      match exit_code with
      | 0 -> ()
      | _ -> failwith ("`ls` exited with " ^ (string_of_int exit_code) ^
          " when looking for older fingerprints file, \
          so it appears that there are no older fingerprints files.")
      end
  | _ -> failwith ("`ls` stopped by a signal while \
      looking for older fingerprints file")
  end;
  prev
;;

let load_fingerprints file =
  try
    load_fingerprints_aux file
  with e1 ->
    let error_str_1 = (Printexc.to_string e1) in
    let moved_filename_msg = begin match e1 with
        | Failure "fingerprint file with an older magic number" ->
            let renamed_file_name = file ^ ".old" in
            (* if renaming fails, then the exception is not caught *)
            Sys.rename file renamed_file_name;
            Printf.sprintf
                "so moved fingerprints file by appending `.old` (%s -> %s)"
                file renamed_file_name
        | Failure "corrupted fingerprint file" ->
            let renamed_file_name = file ^ ".corrupted" in
            (* if renaming fails, then the exception is not caught *)
            Sys.rename file renamed_file_name;
            Printf.sprintf
                "so moved fingerprints file by appending `.corrupted` \
                (%s -> %s)"
                file renamed_file_name
        | End_of_file
        | Failure _ -> (* raised by `Marshal.from_channel` *)
            let renamed_file_name = file ^ ".corrupted" in
            (* if renaming fails, then the exception is not caught *)
            Sys.rename file renamed_file_name;
            Printf.sprintf
                "so moved fingerprints file by appending `.corrupted` \
                (%s -> %s)"
                file renamed_file_name
        | _ -> assert false
    end in
  try
    let prev = previous_fp_file file in
    load_fingerprints_aux prev;
    Errors.err "Cannot load fingerprints file: %s, %s\n\
                previous fingerprints file (%s) loaded \
                (i.e., one with current magic number)\n"
            error_str_1 moved_filename_msg prev;
  with e2 ->
    Errors.err "Cannot load fingerprints file: %s, %s\n\
                Cannot load older fingerprints file: %s\n"
            error_str_1
            moved_filename_msg
            (Printexc.to_string e2);
;;

let print_sti_13 (st, d, pv, zv, iv) =
    let print_floatomega x =
        match x with
        | V13.F f -> printf "%g" f;
        | V13.Omega -> printf "infinity";
    in
    let rec print_meth m =
        match m with
        | V13.Isabelle {
                V13.isabelle_timeout = tmo;
                V13.isabelle_tactic = s} ->
            printf "Isabelle {timeout = ";
            print_floatomega tmo;
            printf "; tactic = %S}" s;
        | V13.Zenon {
                V13.zenon_timeout = t;
                V13.zenon_fallback = m2} ->
            printf "Zenon {timeout = %g; fallback = " t;
            print_meth m2;
            printf "}";
        | V13.Smt -> printf "Smt";
        | V13.SmtT tmo ->
            printf "SmtT (";
            print_floatomega tmo;
            printf ")";
        | V13.Yices -> printf "Yices";
        | V13.YicesT tmo ->
            printf "YicesT (";
            print_floatomega tmo;
            printf ")";
        | V13.Z3 -> printf "Z3";
        | V13.Z3T tmo ->
            printf "Z3T";
            print_floatomega tmo;
            printf ")";
        | V13.Cooper -> printf "Cooper";
        | V13.Sorry -> printf "Sorry";
        | V13.Fail -> printf "Fail";
        | V13.Cvc3T tmo ->
            printf "Cvc3T (";
            print_floatomega tmo;
            printf ")";
        | V13.Smt2lib tmo ->
            printf "Smt2lib (";
            print_floatomega tmo;
            printf ")";
        | V13.Smt2z3 tmo ->
            printf "Smt2z3 (";
            print_floatomega tmo;
            printf ")";
        | V13.Smt3 tmo ->
            printf "Smt3 (";
            print_floatomega tmo;
            printf ")";
        | V13.Z33 tmo ->
            printf "Z33 (";
            print_floatomega tmo;
            printf ")";
        | V13.Cvc33 tmo ->
            printf "Cvc33 (";
            print_floatomega tmo;
            printf ")";
        | V13.Yices3 tmo ->
            printf "Yices3 (";
            print_floatomega tmo;
            printf ")";
        | V13.Verit tmo ->
            printf "Verit (";
            print_floatomega tmo;
            printf ")";
        | V13.Spass tmo ->
            printf "Spass (";
            print_floatomega tmo;
            printf ")";
        | V13.Tptp tmo ->
            printf "Tptp (";
            print_floatomega tmo;
            printf ")";
        | V13.LS4 tmo ->
            printf "LS4 (";
            print_floatomega tmo;
            printf ")";
        | V13.ExpandENABLED ->
            printf "ExpandENABLED";
        | V13.ExpandCdot ->
            printf "ExpandCdot";
        | V13.AutoUSE ->
            printf "Auto-expand definitions";
        | V13.Lambdify ->
            printf "Lambdify definitions";
        | V13.ENABLEDaxioms ->
            printf "ENABLED axioms";
        | V13.LevelComparison ->
            printf "Level Comparison";
        | V13.Trivial ->
            printf "Trivial backend";
    in
    let print_reason r =
        match r with
        | None -> printf "No reason";
        | Some V13.False -> printf "False";
        | Some V13.Timeout -> printf "Timeout";
        | Some V13.Cantwork s -> printf "Cantwork (%S)" s;
    in
    let print_stat s =
        match s with
        | V13.Triv -> printf "Trivial";
        | V13.NTriv (V13.RSucc, m) ->
            printf "RSucc (";
            print_meth m;
            printf ")";
        | V13.NTriv (V13.RFail r, m) ->
            printf "Fail (";
            print_reason r;
            printf ", ";
            print_meth m;
            printf ")";
        | V13.NTriv (V13.RInt, m) ->
            printf "RInt (";
            print_meth m;
            printf ")";
    in
    let print_date (y, m, d, hr, mn, sc) =
        printf "%04d-%02d-%02dT%02d:%02d:%02d" y (m+1) d hr mn sc
    in
    printf "    status = "; print_stat st; printf "\n";
    printf "    date = "; print_date d; printf "\n";
    printf "    tlapm version = %S\n" pv;
    printf "    zenon version = %S\n" zv;
    printf "    isabelle version = %S\n" iv;
;;

let print_fp_line_13r fp str =
  let print_sti_opt lbl o =
    match o with
    | None -> ()
    | Some sti ->
      printf "    %s:\n" lbl;
      print_sti_13 sti;
  in
  printf "  %s :\n" fp;
  print_sti_opt "Trivial" str.V13.tres;
  print_sti_opt "Zenon" str.V13.zres;
  print_sti_opt "Isabelle" str.V13.ires;
  print_sti_opt "SMT" str.V13.smtres;
  print_sti_opt "Cooper" str.V13.cooperres;
  print_sti_opt "Yices" str.V13.yres;
  print_sti_opt "Z3" str.V13.z3res;
  print_sti_opt "CVC3" str.V13.cvc3res;
  print_sti_opt "Smt2lib" str.V13.smt2libres;
  print_sti_opt "Smt2z3" str.V13.smt2z3res;
  print_sti_opt "Smt3" str.V13.smt3res;
  print_sti_opt "Z33" str.V13.z33res;
  print_sti_opt "Cvc33" str.V13.cvc33res;
  print_sti_opt "Yices3" str.V13.yices3res;
  print_sti_opt "Verit" str.V13.veritres;
  print_sti_opt "Spass" str.V13.spassres;
  print_sti_opt "Tptp" str.V13.tptpres;
  print_sti_opt "LS4" str.V13.ls4res;
  print_sti_opt "ExpandENABLED" str.V13.expandenabledres;
  print_sti_opt "ExpandCdot" str.V13.expandcdotres;
  print_sti_opt "Lambdify" str.V13.lambdifyres;
  print_sti_opt "ENABLED axioms" str.V13.enabledaxiomsres;
  print_sti_opt "LevelComparison" str.V13.levelcomparisonres;
;;

let print_fp_line_13l fp stil =
  printf "  %s :\n" fp;
  List.iter print_sti_13 stil;
;;

let iter_file f ic =
  try while true do
    let (fp, stil) = Marshal.from_channel ic in
    f fp stil;
  done with End_of_file -> ()
;;

let print file =
  try
    let ic = open_in_bin file in
    let stop () =
      close_in ic;
      raise Exit;
    in
    let magic = Marshal.from_channel ic in
    printf "Magic number = %d\n" magic;
    if magic <> magic_number then begin
      printf "Fingerprintf file has wrong magic number. Stopping.\n";
      stop ();
    end;
    let v = Marshal.from_channel ic in
    if v >= FPunknown () then begin
      printf "Fingerprint file is from a newer version of tlapm. Stopping.\n";
      stop ();
    end;
    begin match v with
    | FP13 tbl ->
       printf "Fingerprints version = 13\n";
       printf "=========== Hashtable\n";
       Hashtbl.iter print_fp_line_13r tbl;
       printf "=========== Incremental lines\n";
       iter_file print_fp_line_13l ic;
    | _ -> assert false
    end;
    stop ();
  with Exit -> ()
;;

let same_prover p sti =
  match sti with
  | (NTriv (_, m), _, _, _, _) when prover_of_method m = p -> true
  | _ -> false
;;

let erase_results file meth =
  if not (Sys.file_exists file) then Errors.fatal "%s: file not found" file;
  load_fingerprints_aux file;
  let oldtbl = !fptbl in
  fptbl := Hashtbl.create 500;
  let process fp r =
    let p = prover_of_method (meth_to_Vx meth) in
    let keep sti = not (same_prover p sti) in
    let l = List.filter keep (record_to_list r) in
    Hashtbl.add !fptbl fp (list_to_record l);
  in
  Hashtbl.iter process oldtbl;
  let oc = fp_init file [] in
  fp_close_and_consolidate file oc;
;;

let remove fp = Hashtbl.remove !fptbl (fp_to_Vx fp);;

let rec vx_to_st6 st =
  match st with
  | Triv -> Some T.Triv
  | NTriv (sta, meth) ->
     Option.map (fun m -> T.NTriv (vx_to_sta6 sta, m)) (vx_to_meth meth)

and vx_to_sta6 sta =
  match sta with
  | RSucc -> T.RSucc
  | RFail None -> T.RFail None
  | RFail (Some r) -> T.RFail (Some (vx_to_reason r))
  | RInt -> T.RInt

and vx_to_reason r =
  match r with
  | False -> T.False
  | Timeout -> T.Timeout
  | Cantwork s -> T.Cantwork s

and vx_to_meth m =
  match m with
  | Isabelle {isabelle_timeout = tmo; isabelle_tactic = tac} ->
     Some (M.Isabelle (vx_to_floatomega tmo, tac))
  | Zenon {zenon_timeout = tmo; zenon_fallback = m} -> Some (M.Zenon tmo)
  | Smt -> Some (M.SmtT infinity)
  | SmtT tmo -> Some (M.SmtT (vx_to_floatomega tmo))
  | Yices -> Some (M.YicesT infinity)
  | YicesT tmo -> Some (M.YicesT (vx_to_floatomega tmo))
  | Z3 -> Some (M.Z3T infinity)
  | Z3T tmo -> Some (M.Z3T (vx_to_floatomega tmo))
  | Cooper -> Some M.Cooper
  | Sorry -> None
  | Fail -> Some M.Fail
  | Cvc3T tmo -> Some (M.Cvc3T (vx_to_floatomega tmo))
  | Smt2lib tmo -> Some (M.Smt2lib (vx_to_floatomega tmo))
  | Smt2z3 tmo -> Some (M.Smt2z3 (vx_to_floatomega tmo))
  | Smt3 tmo -> Some (M.Smt3 (vx_to_floatomega tmo))
  | Z33 tmo -> Some (M.Z33 (vx_to_floatomega tmo))
  | Cvc33 tmo -> Some (M.Cvc33 (vx_to_floatomega tmo))
  | Yices3 tmo -> Some (M.Yices3 (vx_to_floatomega tmo))
  | Verit tmo -> Some (M.Verit (vx_to_floatomega tmo))
  | Spass tmo -> Some (M.Spass (vx_to_floatomega tmo))
  | Tptp tmo -> Some (M.Tptp (vx_to_floatomega tmo))
  | LS4 tmo -> Some (M.LS4 (vx_to_floatomega tmo))
  | ExpandENABLED -> Some M.ExpandENABLED
  | ExpandCdot -> Some M.ExpandCdot
  | AutoUSE -> Some M.AutoUSE
  | Lambdify -> Some M.Lambdify
  | ENABLEDaxioms -> Some M.ENABLEDaxioms
  | LevelComparison -> Some M.LevelComparison
  | Trivial -> Some M.Trivial

and vx_to_floatomega f =
  match f with
  | Omega -> infinity
  | F x -> x
;;

(* FIXME don't use prover_of_method, but another function that doesn't
   erase the tactic field in the Isabelle case *)

let query fp meth =
  let m = meth_to_Vx meth in
  try
    let l = record_to_list (Hashtbl.find !fptbl (fp_to_Vx fp)) in
    let f (dom, others) (st, _, _, _, _) =
      match st with
      | Triv -> (dom, others)
      | NTriv (_, m2) when prover_of_method m2 <> prover_of_method m ->
         (dom, st :: others)
      | NTriv (RSucc, m2) -> (* FIXME success dominates shorter timeout *)
         (st :: dom, others)
      | NTriv (RFail _, m2) ->
         if get_timeout m2 >= get_timeout m
         then (st :: dom, others)
         else (dom, others)
      | NTriv (RInt, _) -> (dom, others)
    in
    let (dominators, others) = List.fold_left f ([], []) l in
    match dominators with
    | [] -> (None, List.filter_map vx_to_st6 others)
    | x :: _ -> (vx_to_st6 x, List.filter_map vx_to_st6 others)
  with
  | Not_found -> (None, [])
;;

let get_length () = Hashtbl.length !fptbl;;
