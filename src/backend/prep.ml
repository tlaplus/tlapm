(*
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Backend preparations *)

open Ext
open Property

open Expr.T
open Expr.Subst

open Proof.T

open Types

(*let debug = Printf.eprintf;;*)

(*
let debug_time name f x =
  let t0 = Sys.time () in
  try
    let res = f x in
    Printf.eprintf "%s returns; time: %f\n%!" name (Sys.time () -. t0);
    res
  with e ->
    Printf.eprintf "%s raises; time: %f\n%!" name (Sys.time () -. t0);
    raise e
;;
*)

let vprintf fmt =
  if !Params.verbose then
    Printf.kfprintf flush stderr fmt
  else
    Printf.ifprintf stderr fmt

let expand_defs ?(what = fun _ -> true) ob =
  let rec visit sq =
    match Deque.front sq.context with
    | None -> sq
    | Some (h, hs) -> begin
        match h.core with
          | Defn ({core = Operator (nm, e)}, wd, Visible, _) when what wd ->
              visit (app_sequent (scons e (shift 0)) { sq with context = hs })
          | Defn ({core = Bpragma (_, e, _)}, wd, _, _) when what wd ->
              visit (app_sequent (scons e (shift 0)) { sq with context = hs })
          | _ ->
              let sq = visit { sq with context = hs } in
                { sq with context = Deque.cons h sq.context }
      end
  in
  let obl = visit ob.obl.core in
     { ob with obl = { ob.obl with core = obl } }

(*
let expand_defs ?(what = fun _ -> true) ob =
  debug_time "expand_defs" (fun () -> expand_defs ~what ob) ()
;;
*)

(*****************************************************************************)

let nobounds (_, _, ran) = ran = No_domain

let rec extract_equalities e = match e.core with
  | List ((And | Refs), es) -> begin
      let (eqs, es) = List.split (List.map extract_equalities es) in
      let eqs = List.concat eqs in
      let es = List.filter_map (fun x -> x) es in
      match es with
        | [] -> (eqs, None)
        | [e] -> (eqs, Some e)
        | es -> (eqs, Some (List (And, es) @@ e))
    end
  | Apply ({core = Internal Builtin.Conj} as conj, [a ; b]) -> begin
      let (aqs, a) = extract_equalities a in
      let (bqs, b) = extract_equalities b in
      let eqs = aqs @ bqs in
      match a, b with
        | None, None ->
            (eqs, None)
        | ( Some p, None | None, Some p ) ->
            (eqs, Some p)
        | Some a, Some b ->
            (eqs, Some (Apply (conj, [a ; b]) @@ e))
    end
  | Internal Builtin.TRUE ->
      ([], None)
  | Quant (Forall, bs, a) when List.for_all nobounds bs -> begin
      let (eqs, a) = extract_equalities a in
      let eqs = List.map (fun e -> Quant (Forall, bs, e) @@ e) eqs in
      match a with
        | None -> (eqs, None)
        | Some a -> (eqs, Some (Quant (Forall, bs, a) @@ e))
    end
  | Apply ({core = Internal Builtin.Eq}, _) ->
      ([e], None)
  | _ ->
      ([], Some e)

let flatten ob =
  let prefix = ref Deque.empty in
  let rec rewrite sq = match Deque.front sq.context with
    | Some ({core = Fact (e, Visible, tm)} as h, cx) -> begin
        let (eqs, e) = extract_equalities e in
        let k = match e with
          | None -> 0
          | Some e ->
              prefix := Deque.snoc !prefix (Fact (e, Visible, tm) @@ h) ;
              1
        in
        List.iteri begin
          fun n eq ->
            prefix := Deque.snoc !prefix (Fact (app_expr (shift (n + k)) eq, Visible, tm) @@ h)
        end eqs ;
        let sq = { sq with context = cx } in
        let sq = app_sequent (shift (List.length eqs + k - 1)) sq in
        rewrite sq
      end
    | Some (h, cx) ->
        prefix := Deque.snoc !prefix h ;
        rewrite { sq with context = cx }
    | None ->
        sq.active
  in
  let act = rewrite ob.obl.core in
  let sq = { context = !prefix ;
             active = act } in
  { ob with obl = sq @@ ob.obl }


(*****************************************************************************)

let rec rebalance_sequent sq = match sq.active.core with
  | Sequent asq ->
      let sq = { context = Deque.append sq.context asq.context ;
                 active = asq.active }
      in
      rebalance_sequent sq
  | _ ->
      sq

let cleanup =
  let visitor = object (self : 'self)
    inherit [unit] Expr.Visit.map as super

    method expr scx oe = match oe.core with
      | Apply ({core = Internal Builtin.Unprimable}, [e]) ->
          self#expr scx e
      | _ -> super#expr scx oe
  end in
  fun ob ->
    let (_, obl) = visitor#sequent ((), Deque.empty) ob.obl.core in
    let obl = rebalance_sequent obl in
    { ob with obl = obl @@ ob.obl }


(*****************************************************************************)

let mk_timec ob org_ob warnings timeout (prover, tac) =
  fun () ->
    Toolbox.toolbox_print (Lazy.force org_ob) "being proved" prover tac timeout None true None
                          warnings None;
    Schedule.Continue ((fun () -> Schedule.Timeout), timeout)
;;

let mk_donec finished cleanup res_cont warnings =
  fun result time_used ->
    match result with
    | Schedule.Finished -> finished (Some time_used)
    | Schedule.Stopped_kill ->
       !cleanup ();
       res_cont warnings Method.Interrupted (Some time_used)
    | Schedule.Stopped_timeout ->
       !cleanup ();
       res_cont warnings Method.Timedout (Some time_used)
;;

let mk_temps cleanup suffix =
  let (inf, inc) = Util.temp_file cleanup suffix in
  let outf = inf ^ ".out" in
  let outc = open_in_gen [Open_rdonly; Open_creat; Open_binary] 0o777 outf in
  let f () =
    close_in outc;
    Util.rm_temp_file outf;
  in
  Util.add_hook cleanup f ();
  (inf, inc, outf, outc)
;;

let zenon_prove ob org_ob time res_cont =
  let cleanup = ref (fun () -> ()) in
  try
    let (inf, inc, outf, outc) = mk_temps cleanup ".znn" in
    let zcmd =
      Printf.sprintf "%s >%s" (Params.solve_cmd Params.zenon inf) outf
    in
    let in_text =
      ignore (Format.flush_str_formatter ());
      Zenon.pp_print_obligation Format.str_formatter ob;
      Format.flush_str_formatter ()
    in
    output_string inc in_text;
    flush inc;
    let warnings = Errors.get_warnings () in
    let finished time_used =
      let zinput =
        let header = "\n(* BEGIN ZENON INPUT\n" in
        let footer = "\nEND ZENON  INPUT *)\n" in
        Printf.sprintf "%s;; %s\n%s%s" header zcmd in_text footer
      in
      let result = Std.input_all outc in
      !cleanup ();
      if Ext.is_prefix "(* PROOF-FOUND *)" result then
        res_cont warnings (Method.Proved (zinput ^ result)) time_used
      else
        res_cont warnings (Method.Failed "") time_used
    in
    let done_cont = mk_donec finished cleanup res_cont warnings in
    let timo = Printf.sprintf "(%g s)" time in
    let
      time_cont = mk_timec ob org_ob warnings time (Some "zenon", Some timo)
    in
    Schedule.Todo {
      Schedule.line = zcmd;
      Schedule.timeout = float_of_int !Params.wait;
      Schedule.timec = time_cont;
      Schedule.donec = done_cont;
    }
  with Failure msg ->
    !cleanup ();
    let w = Errors.get_warnings () in
    Schedule.Immediate (res_cont w (Method.NotTried msg) None)
;;

let ls4_prove ob org_ob time res_cont =
  let cleanup = ref (fun () -> ()) in
  try
    let (inf, inc, outf, outc) = mk_temps cleanup ".ls4" in
    let cmd =
      Printf.sprintf "%s >%s" (Params.solve_cmd Params.ls4 inf) outf
    in
    let in_text =
      ignore (Format.flush_str_formatter ());
      Ls4.pp_print_obligation Format.str_formatter ob;
      Format.flush_str_formatter ()
    in
    output_string inc in_text;
    flush inc;
    let warnings = Errors.get_warnings () in
    let finished time_used =
      let result = Std.input_all outc in
      !cleanup ();
      if Ext.string_contains result "UNSAT" then
        res_cont warnings (Method.Proved "") time_used
      else
        res_cont warnings (Method.Failed "") time_used
    in
    let done_cont = mk_donec finished cleanup res_cont warnings in
    let timo = Printf.sprintf "(%g s)" time in
    let time_cont = mk_timec ob org_ob warnings time (Some "ls4", Some timo) in
    Schedule.Todo {
      Schedule.line = cmd;
      Schedule.timeout = float_of_int !Params.wait;
      Schedule.timec = time_cont;
      Schedule.donec = done_cont;
    }
  with Failure msg ->
    !cleanup ();
    let w = Errors.get_warnings () in
    Schedule.Immediate (res_cont w (Method.NotTried msg) None)
;;

let isabelle_prove ob org_ob tmo tac res_cont =
  let cleanup = ref (fun () -> ()) in
  try
    let (inf, inc, outf, outc) = mk_temps cleanup ".thy" in
    let thy_path = Filename.chop_extension inf in
    let thy_mod_name = Filename.basename thy_path in
    Isabelle.thy_temp ob tac thy_mod_name inc;
    flush inc;
    let cmdline =
      Printf.sprintf "%s >%s" (Params.solve_cmd Params.isabelle thy_path) outf
    in
    let warnings = Errors.get_warnings () in
    let finished time_used =
      let rec spin log =
        let line = try Some (input_line outc) with End_of_file -> None in
        match line with
        | None -> (false, List.rev log)
        | Some l when Ext.is_prefix "Loading theory" l -> spin []
        | Some l when Ext.is_prefix Params.isabelle_success_string l ->
           (true, [])
        | Some l -> spin (l :: log)
      in
      let (result, log) = spin [] in
      !cleanup ();
      if result then
        let proof = Printf.sprintf "using assms by %s\n" tac in
        res_cont warnings (Method.Proved proof) time_used
      else
        res_cont warnings (Method.Failed "") time_used
    in
    let done_cont = mk_donec finished cleanup res_cont warnings in
    let prov_tac = Method.prover_meth_of_tac (Method.Isabelle (tmo, tac)) in
    let
      time_cont = mk_timec ob org_ob warnings tmo prov_tac
    in
    Schedule.Todo {
      Schedule.line = cmdline;
      Schedule.timeout = float_of_int !Params.wait;
      Schedule.timec = time_cont;
      Schedule.donec = done_cont;
    }
  with Failure msg ->
    !cleanup ();
    let w = Errors.get_warnings () in
    Schedule.Immediate (res_cont w (Method.NotTried msg) None)
;;

(****************************************************************************)

let print_obligation ob =
    let msg = Printf.sprintf "Proof obligation %d :\n" (Option.get ob.id) in
    let pr_obl fmt = ignore (
        let print = Expr.Fmt.pp_print_sequent in
        let cx = (Deque.empty, Ctx.dot) in
        let fmt = Format.std_formatter in
        print cx fmt ob.obl.core) in
    Util.printf
        ~at:ob.obl
        ~prefix:"[INFO]: "
        "%s@\n  @[<b0>%t@]@." msg pr_obl
    (* TODO: conditional printing in more verbose mode of `tlapm`. *)
    (* ignore (sequent_stats ob.obl.core) *)


let log_info (msg: string) =
    let at = noprops "" in
    (* to print `prefix`, set `at <> None` *)
    Util.printf
        ~at:at
        ~prefix:"[INFO]: " "%s" msg


let print_obl_and_msg
        (ob: Proof.T.obligation)
        (msg: string):
            unit =
    (* Print message `msg` and then the obligation `ob`.

    If the obligation is `TRUE` (trivial), then no printing.
    *)
    (* Trivial obligation ?  (for example, a proof directive) *)
    if (((Internal TRUE) <> ob.obl.core.active.core)
        && !Params.verbose) then
    begin
        log_info msg;
        print_obligation ob
    end


let pp_print_ob ?comm:(c=";;") chan ob =
  output_string chan (Printf.sprintf "%s Proof obligation:\n%s" c c);
  let ob_buf = Buffer.create 2000 in
  let fmt = Format.formatter_of_buffer ob_buf in
  Proof.Fmt.pp_print_obligation fmt ob;
  Format.pp_print_flush fmt ();
  let replace inp out = Str.global_replace (Str.regexp_string inp) out in
  let ob_str = replace "\n" ("\n"^c^" ") (Buffer.contents ob_buf) in
  output_string chan ob_str;
  output_string chan "\n"


let spass_unsat_re = Str.regexp "SPASS beiseite: Proof found";;
let eprover_unsat_re = Str.regexp "SZS status Theorem";;
let generic_unsat_re = Str.regexp "^unsat";;

let gen_smt_solve suffix exec desc fmt_expr meth ob org_ob f res_cont comm =
  let cleanup = ref (fun () -> ()) in
  try
    let (inf, inc, outf, outc) = mk_temps cleanup suffix in
    let solver = Params.solve_cmd exec inf in
    let cmdline = Printf.sprintf "%s >%s" solver outf in
    let in_text =
      ignore (Format.flush_str_formatter ());
      fmt_expr Format.str_formatter ob;
      Format.flush_str_formatter ()
		in
    pp_print_ob ~comm:comm inc ob;
    output_string inc in_text;
    flush inc;
    let warnings = Errors.get_warnings () in
    let contains re s =
      try ignore (Str.search_forward re s 0); true
      with Not_found -> false
    in
    let is_unsat res =
      contains generic_unsat_re res
      || contains spass_unsat_re res
      || contains eprover_unsat_re res
    in
    let finished time_used =
      let res = Std.input_all outc in
      !cleanup ();
      if is_unsat res then
        res_cont warnings (Method.Proved "") time_used
      else if Ext.is_prefix "sat" res
              || Ext.is_prefix "unknown" res
      then begin
        let msg = "(* SMT failed with status = " ^ res ^ " *)\n" in
        res_cont warnings (Method.Failed msg) time_used
      end else begin
        res_cont warnings (Method.Failed "") time_used
      end
    in
    let done_cont = mk_donec finished cleanup res_cont warnings in
    let prov_tac = Method.prover_meth_of_tac meth in
    let time_cont = mk_timec ob org_ob warnings f prov_tac in
    Schedule.Todo {
      Schedule.line = cmdline;
      Schedule.timeout = float_of_int !Params.wait;
      Schedule.timec = time_cont;
      Schedule.donec = done_cont;
    }
  with
  | Failure msg ->
    !cleanup ();
    let w = Errors.get_warnings () in
    Schedule.Immediate (res_cont w (Method.NotTried msg) None)
  | Util.Internal_timeout as e ->
     !cleanup ();
     raise e;
  | e ->
    let backtrace = Printexc.get_backtrace () in
    !cleanup ();
    let w =
      Printf.sprintf "%s\nUnexpected exception: %s\n%s" (Errors.get_warnings ())
                     (Printexc.to_string e) backtrace
    in
    let msg = "Unexpected error in SMT back-end" in
    Schedule.Immediate (res_cont w (Method.NotTried msg) None)
;;

let smt_solve ob org_ob f res_cont =
  gen_smt_solve ".smt" Params.smt "default SMT solver" Smt.encode_smtlib
                (Method.Smt3 f) ob org_ob f res_cont ";;"
;;

let cvc3_solve ob org_ob f res_cont =
  gen_smt_solve ".smt" Params.cvc4 "CVC4" Smt.encode_smtlib
                (Method.Cvc33 f) ob org_ob f res_cont ";;"
;;

let yices_solve ob org_ob f res_cont =
  gen_smt_solve ".ys" Params.yices "Yices" Smt.encode_smtlib
                (Method.Yices3 f) ob org_ob f res_cont ";;"
;;

let z3_solve ob org_ob f res_cont =
  gen_smt_solve ".smt2" Params.z3 "Z3" (Smt.encode_smtlib ~solver:"Z3")
                (Method.Z33 f) ob org_ob f res_cont ";;"
;;

let verit_solve ob org_ob f res_cont =
  gen_smt_solve ".smt2" Params.verit "veriT" Smt.encode_smtlib
                (Method.Verit f) ob org_ob f res_cont ";;"
;;

let spass_solve ob org_ob f res_cont =
  gen_smt_solve ".tptp" Params.spass_tptp "Spass" Smt.encode_fof
                (Method.Spass f) ob org_ob f res_cont "%%"
;;

let tptp_solve ob org_ob f res_cont =
  gen_smt_solve ".tptp" Params.eprover "Tptp" Smt.encode_fof
                (Method.Tptp f) ob org_ob f res_cont "% "
;;

(*****************************************************************************)

exception Nontrivial

let rec find_fact cx e rest =
  match Deque.rear cx with
  | Some (cx, ({core = Fact (f, _, tm)} as fac)) ->
      let e = app_expr (shift (-1)) e in
      if Expr.Eq.expr f e then
        let cx = Deque.snoc cx (Fact (f, Visible, tm) @@ fac) in
        let cx = Deque.append_list cx rest in
        cx
      else find_fact cx e (fac :: rest)
  | Some (cx, ({core = Fresh (hx, shp, hk, Bounded (ran, _))} as frs)) ->
      let f = Apply begin
        Internal Builtin.Mem @@ nowhere,
        [ Ix 1 @@ nowhere
        ; app_expr (shift 1) ran]
      end @@ nowhere in
      if Expr.Eq.expr f e then
        let cx =
          Deque.snoc cx (Fresh (hx, shp, hk, Bounded (ran, Visible)) @@ frs)
        in
        let cx = Deque.append_list cx rest in
        cx
      else find_fact cx (app_expr (shift (-1)) e) (frs :: rest)
  | Some (cx, h) ->
      find_fact cx (app_expr (shift (-1)) e) (h :: rest)
  | None ->
      raise Nontrivial

let trying_to_prove_true = function
  | Internal Builtin.TRUE -> true
  | _ -> false

(* [trivial expanded obligation]
   Check the triviality of [obligation].
   If it is not trivial, raise Nontrivial.
   If it is trivial, return a proof that lets Isabelle check the
       triviality, with or without expanded defintions, depending on
       [expanded]
  @raise Nontrivial
*)
(* FIXME printing should probably be done in save_result *)
let trivial ob =
  match ob.kind with
  | Ob_main -> raise Nontrivial
  | Ob_support ->
      let sq = ob.obl.core in
      let cx = if (trying_to_prove_true sq.active.core)
        then sq.context
        else find_fact sq.context sq.active [] in
      vprintf "(* ... trivial *)\n" ;
      let sq = { sq with context = cx } in
      let prob = { ob with obl = sq @@ ob.obl } in
      Toolbox.print_new_res prob Triv "" None;
      {
        Types.final_form = prob;
        Types.log = ["trivial"];
        Types.proof = "";
        Types.results = [Types.Triv];
      }
  | Ob_error msg ->
      let res = NTriv (RFail (Some (Cantwork "user error")), Method.Fail) in
      Toolbox.print_new_res ob res "" None;
      {
        final_form = ob;
        log = ["error"];
        proof = "";
        results = [res];
      }
;;

(******************************************************************************)


let get_prover_name m =
  match m with
  | Method.Zenon _ -> "Zenon"
  | Method.LS4 _ -> "LS4"
  | Method.Isabelle _ -> "Isabelle"
  | Method.SmtT _ -> "SMT"
  | Method.YicesT _ -> "Yices"
  | Method.Z3T _ -> "Z3"
  | Method.Cvc3T _ -> "CVC3"
  | Method.Cooper -> "Cooper"
  | Method.Fail -> "Fail"
  | Method.Smt2lib _ -> "Smt2lib"
  | Method.Smt2z3 _ -> "Smt2z3"
  | Method.Smt3 _ -> "SMT3"
  | Method.Z33 _ -> "Z33"
  | Method.Cvc33 _ -> "CVC33"
  | Method.Yices3 _ -> "Yices3"
  | Method.Verit _ -> "Verit"
  | Method.Spass _ -> "Spass"
  | Method.Tptp _ -> "TPTP"
  | Method.ExpandENABLED -> "ExpandENABLED"
  | Method.ExpandCdot -> "ExpandCdot"
  | Method.AutoUSE -> "AutoUSE"
  | Method.Lambdify -> "Lambdify"
  | Method.ENABLEDaxioms -> "ENABLEDaxioms"
  | Method.LevelComparison -> "LevelComparison"
  | Method.Trivial -> "Trivial"
;;

let already_processed ob meth =
  let fp = Option.get ob.fingerprint in
  let loc = Option.get (Util.query_locus ob.Proof.T.obl) in
  if !Params.no_fp || !Params.nofp_sl-1 < Loc.line loc.Loc.start
                      && Loc.line loc.Loc.stop < !Params.nofp_el+1
  then begin
    Fpfile.remove fp;
    (Some meth, [])
  end else begin
    let success_warning m1 m2 =
      let f1 = Method.timeout m1 in
      let f2 = Method.timeout m2 in
      let prover = get_prover_name m2 in
      if f1 < f2 then
        Errors.err ~at:ob.Proof.T.obl
                   "%s already succeeded in proving that obligation with \
                    a longer timeout (%g seconds).\n\
                    If you want to relaunch %s on that obligation with a \
                    shorter timeout, use the \"Launch prover\" command to \
                    forget previous results." prover f2 prover;
    in
    match Fpfile.query fp meth with
        (* No fingerprint *)
    | (None, others) -> (Some meth, [])
        (* Successful proof already *)
    | (Some (NTriv (RSucc, m) as st), others) ->
       success_warning meth m;
       (None, [st])
       (* No proof, fingerprint exists *)
    | (Some (NTriv ((RFail r), m)), others) -> (None, [NTriv ((RFail r), m)])
        (* Interrupted, fingerprint exists *)
    | (Some (NTriv (RInt, m)), others) -> (None, [NTriv (RInt, m)])
    | (Some Triv, others) -> (None, [Triv])
        (*
    | (Some st, others) -> (None, [st])
    *)
  end
;;

(*******************************************************************)

let make_methname meth =
  Format.pp_print_string Format.str_formatter "attempted " ;
  Method.pp_print_tactic Format.str_formatter meth ;
  Format.flush_str_formatter ()


let make_res_cont org_ob meth save =
  let methname = make_methname meth in
  let res_cont
        (warnings: string)
        (res: Method.result)
        (time_used: float option):
            bool =
      match res with
      | Method.Proved prf ->
         let res = NTriv (RSucc, meth) in
         Toolbox.print_new_res
            (Lazy.force org_ob) res warnings time_used;
         save methname prf res;
         (* FIXME call success function *)
         true
      | Method.Failed msg ->
         (* `res` has type `status_type6` of
         `status_type_aux6 * Method.t`
         and
         `status_type_aux6` has value
         `RFail of reason option`
         and `reason option` has values
         `None`
         `Some False`
         `Some Timeout`
         `Some (Cantwork of string)`
         *)
         let res = NTriv (RFail (Some False), meth) in
         Toolbox.print_new_res
            (Lazy.force org_ob) res (warnings ^ msg) time_used;
         save methname "" res;
         false
      | Method.Timedout ->
         let res = NTriv (RFail (Some Timeout), meth) in
         Toolbox.print_new_res
            (Lazy.force org_ob) res warnings time_used;
         save methname "" res;
         false
      | Method.Interrupted ->
         let res = NTriv (RInt, meth) in
         Toolbox.print_new_res
            (Lazy.force org_ob) res warnings time_used;
         save methname "" res;
         false
      | Method.NotTried msg ->
         let res = NTriv (RFail (Some (Cantwork msg)), meth) in
         Toolbox.print_new_res
            (Lazy.force org_ob) res warnings time_used;
         save methname "" res;
         false
    in
    res_cont


let prove_with ob org_ob meth save =  (* FIXME add success fuction *)
  let methname = make_methname meth in
  let res_cont = make_res_cont org_ob meth save
  in
  match meth with
  | Method.Zenon f ->
     if !Params.verbose then begin
       let (_, zv, _) = Option.get !Params.zenon_version in
       vprintf "(* ... using zenon version [%d] (timeout: %fs) *)\n" zv f
     end;
     zenon_prove ob org_ob f res_cont
  | Method.LS4 f ->
     vprintf "(* ... using LS4 *)\n";
     ls4_prove ob org_ob  f res_cont
  | Method.Isabelle (tmo, tac) ->
     vprintf "(* ... using isabelle tactic %s (%g s) *)\n" tac tmo;
     isabelle_prove ob org_ob tmo tac res_cont
  | Method.SmtT f -> (* FIXME remove *)
     vprintf "(* ... using the default SMT solver *)\n" ;
     smt_solve ob org_ob f res_cont
  | Method.Cvc3T f -> (* FIXME remove *)
     vprintf "(* ... using CVC3 *)\n" ;
     cvc3_solve ob org_ob f res_cont
  | Method.YicesT f -> (* FIXME remove *)
     vprintf "(* ... using Yices *)\n" ;
     yices_solve ob org_ob f res_cont
  | Method.Z3T f -> (* FIXME remove *)
     vprintf "(* ... using Z3 *)\n" ;
     z3_solve ob org_ob f res_cont
  | Method.Smt2lib f -> (* FIXME remove *)
     vprintf "(* ... using SMTLIB(2) *)\n" ;
     smt_solve ob org_ob f res_cont
  | Method.Smt2z3 f ->
     vprintf "(* ... using Z3(2) *)\n" ;
     z3_solve ob org_ob f res_cont
  | Method.Smt3 f ->
     vprintf "(* ... using SMT(v3) *)\n" ;
     smt_solve ob org_ob f res_cont
  | Method.Z33 f ->
     vprintf "(* ... using Z3(v3) *)\n" ;
     z3_solve ob org_ob f res_cont
  | Method.Cvc33 f ->
     vprintf "(* ... using CVC4(v3) *)\n" ;
     cvc3_solve ob org_ob f res_cont
  | Method.Yices3 f ->
     vprintf "(* ... using Yices(v3) *)\n" ;
     yices_solve ob org_ob f res_cont
  | Method.Verit f ->
     vprintf "(* ... using Verit *)\n" ;
     verit_solve ob org_ob f res_cont
  | Method.Spass f ->
     vprintf "(* ... using Spass *)\n" ;
     spass_solve ob org_ob f res_cont
  | Method.Tptp f ->
     vprintf "(* ... using default TPTP prover *)\n" ;
     tptp_solve ob org_ob f res_cont
  | Method.Cooper ->
     vprintf "(* ... using Cooper's method *)\n" ;
     Errors.warn "Cooper's method is not available any more.\n";
     let res = NTriv (RFail None, meth) in
     Toolbox.print_new_res ob res (Errors.get_warnings ()) None;
     save methname "" res;
     Schedule.Immediate false
  | Method.ExpandENABLED ->
     (* TODO: use `Util.printf` ? *)
     print_string "(* ... unexpected expansion of `ENABLED` *)\n";
     assert false
  | Method.ExpandCdot ->
     print_string "(* ... unexpected expansion of `\\cdot` *)\n";
     assert false
  | Method.AutoUSE ->
     print_string "(* ... unexpected auto-expansion of definitions *)\n";
     assert false
  | Method.Lambdify ->
     print_string "(* ... unexpected lambdification *)\n";
     assert false
  | Method.ENABLEDaxioms ->
     print_string "(* ... unexpected application of `ENABLED` axioms *)\n";
     assert false
  | Method.LevelComparison ->
     print_string "(* ... unexpected level comparison *)\n";
     assert false
  | Method.Trivial ->
     vprintf "%s" ("(* ... using only TLAPM " ^
        "(trivial backend:  `Schedule.Immediate true` ) *)\n");
     Schedule.Immediate true
  | Method.Fail ->
     vprintf "(* ... failing *)\n" ;
     Schedule.Immediate false
;;

(*****************************************************************************)


(* For reading, the function `Tlapm.process_obs.record`,
which is called from within the function `save_result` below.
*)
(*
let record
        (success: bool)
        (ob: Proof.T.obligation) =
    (* the number `obl_id \in Nat` that identifies the obligation `ob` *)
    let obl_id = Option.get ob.id in
    (* store the obligation id number in the internal table `treated` *)
    treated := IntSet.add obl_id !treated;
    (* if the prover (frontend or backend) succeeded, *)
    if success then (* then store the obligation id number in
                    the internal table `proved`
                    *)
        proved := IntSet.add obl_id !proved;
*)


let save_result fpout thyout record (r: package) =
    (* `record` is the function `Tlapm.process_obs.record` *)
    if r.proof <> "" then Isabelle.thy_write thyout r.final_form r.proof;
    (* write fingerprint and results to the fingerprints file `fpout` *)
    let fingerprint: string = Option.get r.final_form.fingerprint in
    Fpfile.fp_writes
        fpout fingerprint r.results;
    (* write results to the internal table `Tlapm.process_obs.treated` and
    only those obligations whose proof succeeded in the internal table
    `Tlapm.process_obs.proved`
    *)
    let f res =
        match res with
        | Types.Triv
        | Types.NTriv (Types.RSucc, _) ->
            record true r.final_form
        | _ ->
            record false r.final_form  (* filter obligations that have not been
                proved, so that they are not added to the `IntSet` `proved`.
                *)
        in
    List.iter f r.results;
;;

(*
type Proot.T.obligation = {
    id  : int option;
    obl : sequent wrapped;
    fingerprint : string option;
    kind : obligation_kind;
}
*)


let expr_from_obl
        (ob: Proof.T.obligation):
            Expr.T.expr =
    (* Return expression for the sequent of the proof obligation `obl`. *)
    let sequent_wrapped: Expr.T.sequent wrapped = ob.obl in
    let sequent: Expr.T.sequent = sequent_wrapped.core in
    let expr_: Expr.T.expr_ = Sequent sequent in
    (* let expr: Expr.T.expr = noprops expr_ in *)
    expr_ @@ ob.obl


let obl_from_expr
        (expr: Expr.T.expr)
        (ob: Proof.T.obligation):
            Proof.T.obligation =
    (* Return proof obligation `obl` with the sequent from `expr`. *)
    match expr.core with
    | Sequent sequent ->
        let sequent_wrapped = {ob.obl with core = sequent} in
        (* the properties of `ob.obl` are propagated, because they are used in
        Toolbox messages.
        *)
        {ob with obl = sequent_wrapped}
    | _ -> failwith "Backend.Prep.obl_from_expr"


let normalize_expr ob =
    print_obl_and_msg ob (
        "Proof obligation before `Backend.Prep.expand_defs`:\n");
    let ob = expand_defs ob in
    print_obl_and_msg ob (
        "Proof obligation after `Backend.Prep.expand_defs` and " ^
        "before `Expr.Elab.normalize`:\n");
    let expr: Expr.T.expr =
        let expr = expr_from_obl ob in
        let cx = Deque.empty in
        Expr.Elab.normalize cx expr in
    let ob = obl_from_expr expr ob in
    print_obl_and_msg ob "Proof obligation after `Expr.Elab.normalize`:\n";
    ob


let invert_renaming ob =
    (* Map parameter names in `\E` bounds to variable names. *)
    let expr = expr_from_obl ob in
    let expr =
        let cx = Deque.empty in
        Expr.Action.invert_renaming cx expr in
    let ob = obl_from_expr expr ob in
    ob


let expand_enabled_cdot ob
        ~(expand_enabled:bool)
        ~(expand_cdot:bool)
        ~(autouse: bool)
        ~(apply_lambdify: bool)
        ~(enabled_axioms: bool)
        ~(level_comparison: bool) =
    (* Instantiate modules, use de Bruijn indices, expand action operators,
    automatically expand definitions necessary for soundness of expanding
    the operators `ENABLED` and `\cdot`.
    *)
    print_obl_and_msg ob (
        "Proof obligation before `Expr.Action.expand_action_operators`:\n");
    let expr = expr_from_obl ob in
    let expr: Expr.T.expr = begin
        if expand_enabled || expand_cdot then begin
            let cx = Deque.empty in
            Expr.Action.expand_action_operators
            (* Expr.Action_quadratic.expand_action_operators *)
            (* Expr.Action_iter.expand_action_operators *)
                cx expr
                ~expand_enabled:expand_enabled
                ~expand_cdot:expand_cdot
                ~autouse:autouse
        end
        else if apply_lambdify then begin
            let cx = Deque.empty in
            Expr.Action.lambdify
                cx expr
                ~lambdify_enabled:apply_lambdify
                ~lambdify_cdot:apply_lambdify
                ~autouse:autouse
        end
        else if level_comparison then begin
            let cx = Deque.empty in
            Expr.LevelComparison.check_level_change
                cx expr
        end
        else if enabled_axioms then begin
            if Expr.T.has_enabledaxioms expr then begin
                print_string "expr has ENABLEDaxioms property ===\n";
                if not (Expr.T.get_enabledaxioms ob.obl) then
                    failwith "ENABLEDaxioms depends on assumptions of level > 1 \n\n"
                end;
            let cx = Deque.empty in
            Expr.Action.implication_to_enabled cx expr
        end
        else
            expr
        end in
    let ob = obl_from_expr expr ob in
    print_obl_and_msg ob (
        "Proof obligation after `Expr.Action.expand_action_operators` " ^
        "(expansion of `ENABLED`, `\\cdot`, and definitions for soundness):\n");
    ob


let normalize_expand ob fpout thyout record
        ~(expand_enabled:bool)
        ~(expand_cdot:bool)
        ~(autouse: bool)
        ~(apply_lambdify: bool)
        ~(enabled_axioms: bool)
        ~(level_comparison: bool) =
    let ob = normalize_expr ob in
    try
        let ob = expand_enabled_cdot
            ob
            ~expand_enabled:expand_enabled
            ~expand_cdot:expand_cdot
            ~autouse:autouse
            ~apply_lambdify:apply_lambdify
            ~enabled_axioms:enabled_axioms
            ~level_comparison:level_comparison in
        (ob, true)
    with Failure msg ->
        (* `msg` is the message from soundness checks,
        which describes which soundness check failed,
        and how the input module could possibly be changed to
        pass the soundness check.
        *)
    begin
        assert (expand_enabled || expand_cdot || apply_lambdify
            || enabled_axioms || level_comparison);
        (* !cleanup (); *)
        (* let warnings: string = Errors.get_warnings () in *)
        let warnings = (msg ^ "\nObligation:\n\n") in
            (* `warnings` is prepended to
            the obligation, within the Toolbox message that is printed by the
            function `Backend.Toolbox.toolbox_print`.

            This assignment results in `msg` appearing in the Toolbox message
            both:

            - in the field `@!!reason:`, and

            - in the field `@!!obl:`, prepended to the obligation.
            *)
        let res_cont =
            (* TODO: consider case of multiple frontends,
            and whether to iterate through all the frontends and
            record the results in the fingerprints file
            *)
            let meth = if expand_enabled then
                            Method.ExpandENABLED
                        else if expand_cdot then begin
                            Method.ExpandCdot
                        end else if apply_lambdify then begin
                            Method.Lambdify
                        end else if enabled_axioms then begin
                            Method.ENABLEDaxioms
                        end else begin
                            assert level_comparison;
                            Method.LevelComparison
                        end
                    in
            let save log proof res =
                let r = {
                    Types.final_form = ob;
                    Types.log = [log];
                    Types.proof = proof;
                    Types.results = [res];
                    } in
                save_result fpout thyout record r
                in
            make_res_cont (lazy ob) meth save
            in
        (* let result: Method.result = Method.Proved msg in *)
        let result: Method.result = Method.NotTried msg in
        (* let result: Method.result = Method.Failed "" in *)
        let time_used: float option = None in
        let _ = res_cont warnings result time_used in
        ();
        (* assert false; *)
        (* let schedule: Schedule.computation = Schedule.Immediate false
        in ignore schedule ; *)
        let new_seq =
                {ob.obl.core with active = noprops (Internal Builtin.FALSE)}
            in
        let ob = {ob with obl = {ob.obl with core = new_seq}} in
        (ob, false)
    end
;;

(*
let normalize ob = debug_time "normalize" normalize ob;;
*)

(*****************************************************************************)

type meth_or_premeth =
  | Meth of Method.t
  | Premeth of (Util.hint * backend_args) list list

let compute_meth def args usept =
  let prover = ref None in
  let prover_loc = ref None in
  let timeout = ref None in
  let tactic = ref None in
  let rec read def args =
    match def with
    | [] ->
       if args <> [] then begin
         Errors.err ~at:usept "Too many arguments";
         raise Exit;
       end;
    | ({core = "prover"} as defpt, a) :: t ->
       begin match a with
       | Bstring s ->
          prover := Some s;
          prover_loc := Some (() @@ defpt);
          read t args;
       | Bdef ->
          begin match args with
          | {core = String s} :: tt ->
             prover := Some s;
             prover_loc := Some (() @@ usept);
             read t tt;
          | x :: tt ->
             Errors.err ~at:x "This argument should be a string (prover name)";
             raise Exit;
          | [] ->
             Errors.err ~at:usept "Some arguments are missing";
             raise Exit;
          end
       | _ ->
          Errors.err ~at:defpt "Argument should be a string or @";
          raise Exit;
       end
    | ({core = "timeout"} as defpt, a) :: t ->
       begin match a with
       | Bfloat f ->
          timeout := Some f;
          read t args;
       | Bdef ->
          begin match args with
          | {core = Num (s1, s2)} :: tt ->
             timeout := Some (float_of_string (Printf.sprintf "%s.%s" s1 s2));
             read t tt;
          | x :: tt ->
             Errors.err ~at:x "This argument should be a number (timeout)";
             raise Exit;
          | [] ->
             Errors.err ~at:usept "Some arguments are missing";
             raise Exit;
          end
       | _ ->
          Errors.err ~at:defpt "Argument should be a number or @";
          raise Exit;
       end
    | ({core = "tactic"} as defpt, a) :: t ->
       begin match a with
       | Bstring s ->
          tactic := Some s;
          read t args
       | Bdef ->
          begin match args with
          | {core = String s} :: tt ->
             tactic := Some s;
             read t tt;
          | x :: tt ->
             Errors.err ~at:x "This argument should be a string (proof tactic)";
             raise Exit;
          | [] ->
             Errors.err ~at:usept "Some arguments are missing";
             raise Exit;
         end
       | _ ->
          Errors.err ~at:defpt "Argument should be a string or @";
          raise Exit;
       end
    | ({core = kwd} as defpt, a) :: t ->
       Errors.err ~at:defpt
                  "Unknown keyword in proof method definition: %s" kwd;
       raise Exit;
  in
  begin try read def args;
  with Exit -> failwith "error in prover specification"
  end;
  match !prover with  (* FIXME should factor with Params.mk_meth *)
  | Some "zenon" ->
     let tmo = Option.default Method.default_zenon_timeout !timeout in
     Method.Zenon tmo
  | Some "isabelle" ->
     let tmo = Option.default Method.default_isabelle_timeout !timeout in
     let tac = Option.default "auto" !tactic in
     Method.Isabelle (tmo, tac)
  | Some "yices" ->
     let tmo = Option.default Method.default_yices_timeout !timeout in
     Method.Yices3 tmo;
  | Some "ls4" ->
     let tmo = Option.default Method.default_ls4_timeout !timeout in
     Method.LS4 tmo;
  | Some "z3" ->
     let tmo = Option.default Method.default_z3_timeout !timeout in
     Method.Z33 tmo;
  | Some "smt" ->
     let tmo = Option.default Method.default_smt_timeout !timeout in
     Method.Smt3 tmo;
  | Some "cvc3" ->
     let tmo = Option.default Method.default_cvc3_timeout !timeout in
     Method.Cvc33 tmo;
  | Some "cooper" -> Method.Cooper
  | Some "fail" -> Method.Fail
  | Some "smt2lib" ->
     let tmo = Option.default Method.default_smt2_timeout !timeout in
     Method.Smt3 tmo
  | Some "smt2z3" ->
     let tmo = Option.default Method.default_smt2_timeout !timeout in
     Method.Z33 tmo
  | Some "smt3" ->
     let tmo = Option.default Method.default_smt2_timeout !timeout in
     Method.Smt3 tmo
  | Some "z33" ->
     let tmo = Option.default Method.default_smt2_timeout !timeout in
     Method.Z33 tmo
  | Some "cvc33" ->
     let tmo = Option.default Method.default_smt2_timeout !timeout in
     Method.Cvc33 tmo
  | Some "yices3" ->
     let tmo = Option.default Method.default_smt2_timeout !timeout in
     Method.Yices3 tmo
  | Some "verit" ->
     let tmo = Option.default Method.default_smt2_timeout !timeout in
     Method.Verit tmo
  | Some "spass" ->
     let tmo = Option.default Method.default_spass_timeout !timeout in
     Method.Spass tmo
  | Some "tptp" ->
     let tmo = Option.default Method.default_tptp_timeout !timeout in
     Method.Tptp tmo
  | Some "expandenabled" ->
     Method.ExpandENABLED
  | Some "expandcdot" ->
     Method.ExpandCdot
  | Some "autouse" ->
     Method.AutoUSE
  | Some "lambdify" ->
     Method.Lambdify
  | Some "enabledaxioms" ->
     Method.ENABLEDaxioms
  | Some "levelcomparison" ->
     Method.LevelComparison
  | Some "trivial" ->
     Method.Trivial
  | Some s ->
     Errors.err ?at:!prover_loc "Unknown prover: %s" s;
     failwith "error in prover specification";
  | None ->
     let defpt =
       match def with
       | [] -> assert false  (* the parser ensures this cannot happen *)
       | (defpt, _) :: _ -> defpt
     in
     Errors.err ~at:defpt "Missing prover name";
     failwith "error in prover specification";
;;

let find_meth ob =
  match query ob.obl Proof.T.Props.meth with
  | Some _ -> ob
  | None ->
     let meths = ref [] in
     let use_loc = ref Loc.unknown in
     let stack : (meth_or_premeth option) list ref = ref [] in
     let f n h =
       match h.core with
       | Fact ({core = With (_, m)} as fac, Visible, tm) -> (* FIXME remove *)
          meths := [m] :: !meths ;
          stack := None :: !stack;
          Fact (fac, Visible, tm) @@ h
       | Defn ({core = Bpragma (h, e, l)} as def,
                wheredef, visibility, export) ->
           stack := Some (Premeth (l)) :: !stack;
           Defn (def, wheredef, visibility, export) @@ h
       | Fact ({core = Apply ({core = Ix n}, ll)} as fac, Visible, tm) ->
          begin match List.nth !stack (n-1) with
          | None ->
             stack := None :: !stack;
             Fact (fac, Visible, tm) @@ h
          | Some (Premeth (l)) ->
             if Property.get h Proof.T.Props.use_location != !use_loc then begin
               meths := [];
               use_loc := Property.get h Props.use_location;
             end;
             let f x = compute_meth x ll fac in
             meths := (List.map f l) :: !meths;
             stack := None :: !stack;
             Fact (fac, Visible, tm) @@ h
          | Some (Meth _) -> assert false  (* FIXME remove *)
          end
       | Defn ({core = Operator (h, {core = With (exp, m)})} as def,
               wheredef, Visible, export) ->  (* FIXME remove *)
          stack := Some (Meth m) :: !stack;
          Defn (def, wheredef, Visible, export) @@ h
       | Fact ({core = Ix n} as fac, Visible, tm) ->
          begin match List.nth !stack (n-1) with
          | None ->
             stack := None :: !stack;
             Fact (fac, Visible, tm) @@ h
          | Some (Meth m) ->          (* FIXME remove *)
             meths := [m] :: !meths;
             stack := None :: !stack;
             Fact (fac, Visible, tm) @@ h  (* was `Hidden` *)
          | Some (Premeth (l)) ->
             if Property.get h Proof.T.Props.use_location != !use_loc then begin
               meths := [];
               use_loc := Property.get h Props.use_location;
             end;
             let f x = compute_meth x [] fac in
             meths := (List.map f l) :: !meths;
             stack := None :: !stack;
             Fact (fac, Visible, tm) @@ h
          end
       | _ ->
          stack := None :: !stack;
          h
     in
     let cx = Deque.map f ob.obl.core.context in
     let meths =
        match !meths with
        | [] -> !Params.default_method
        | m -> List.flatten (List.rev m)
     in
     let prover_meths = List.filter
         (fun x -> (
             (x <> Method.ExpandENABLED) &&
             (x <> Method.ExpandCdot) &&
             (x <> Method.AutoUSE) &&
             (x <> Method.Lambdify) &&
             (x <> Method.ENABLEDaxioms) &&
             (x <> Method.LevelComparison)
             ))
         meths in
     let meths =
       match prover_meths with
       | [] -> List.append meths !Params.default_method
       | m -> meths
     in
     let sq = { context = cx ; active = ob.obl.core.active } in
     let obl = sq @@ ob.obl in
     let obl = assign obl Proof.T.Props.meth meths in
     { ob with obl = obl }
;;

let really_ship ob org_ob meth fpout thyout record =
  if !Params.printallobs then begin
    let tt = match meth with
    | Method.LS4 _ -> true
    | _ -> false in
    (* FIXME "normalized" not allowed in protocol (?) *)
    Toolbox.toolbox_print (Lazy.force org_ob) ~temp:tt "normalized" None None
                          (Method.timeout meth) None true None "" None;
  end;
  if !Params.noproving then
    Schedule.Immediate false
  else begin
    let ob = Lazy.force ob in
    let ob = if !Params.ob_flatten then flatten ob else ob in
    let save log proof res =
      let r = {
        Types.final_form = ob;
        Types.log = [log];
        Types.proof = proof;
        Types.results = [res];
      } in
      save_result fpout thyout record r
    in
    prove_with ob org_ob meth save
  end
;;

(* TODO: constness visitor also called in frontends *)
let add_constness ob =
  let e = noprops (Expr.T.Sequent ob.obl.core) in
  let visitor = object (self: 'self)
    inherit Expr.Constness.const_visitor
  end in
  match visitor#expr ((), Deque.empty) e with
  | {core = Expr.T.Sequent sq} -> {ob with obl = sq @@ ob.obl}
  | _ -> assert false
;;

let is_success st =
  match st with
  | Triv -> true  (* FIXME assert false -- trivial results are not in FP *)
  | NTriv (RSucc, _) -> true
  | _ -> false
;;

let is_trivial x =
  try ignore (Lazy.force x); true with Nontrivial -> false
;;


(* This function is called on every obligation in the range selected by the
   user. It produces a [Schedule.t] that represents the job of proving this
   obligation.
*)
let ship ob fpout thyout record =
  vprintf "(* trying obligation %d generated from %s *)\n" (Option.get ob.id)
          (Util.location ~cap:false ob.obl);
  begin try
    print_obl_and_msg ob "Proof obligation before `find_meth`:\n";
    let ob = find_meth ob in
    print_obl_and_msg ob "Proof obligation after `find_meth`:\n";
    let meths = get ob.obl Proof.T.Props.meth in
    let expand_enabled = List.exists
        (fun x -> (x = Method.ExpandENABLED)) meths in
    let expand_cdot = List.exists
        (fun x -> (x = Method.ExpandCdot)) meths in
    let autouse = List.exists
        (fun x -> (x = Method.AutoUSE)) meths in
    let apply_lambdify = List.exists
        (fun x -> (x = Method.Lambdify)) meths in
    let enabled_axioms = List.exists
        (fun x -> (x = Method.ENABLEDaxioms)) meths in
    let level_comparison = List.exists
        (fun x -> (x = Method.LevelComparison)) meths in
    let meths = List.filter
        (fun x -> (
            (x <> Method.ExpandENABLED) &&
            (x <> Method.ExpandCdot) &&
            (x <> Method.AutoUSE) &&
            (x <> Method.Lambdify) &&
            (x <> Method.ENABLEDaxioms) &&
            (x <> Method.LevelComparison)
            ))
        meths in
    assert ((List.length meths) > 0);
    (* compute fingerprint:
        The fingerprint is computed before:
            - expanding definitions listed in `BY DEF`
            - normalizing expressions
            - auto-expanding definitions for sound `ENABLED`, `\cdot` expansion
            - replacing `ENABLED` and `\cdot` with rigid quantification
        The fingerprints include both the assertion and `BY` statement
        proof directives.
        *)
    let const_fp_ob =
      lazy (Fingerprints.write_fingerprint (add_constness ob))
    in
    let p = lazy (normalize_expand (Lazy.force const_fp_ob)
            fpout thyout record
            ~expand_enabled
            ~expand_cdot
            ~autouse
            ~apply_lambdify
            ~enabled_axioms
            ~level_comparison)
    in
    let prep_meth m =
      let ob = Lazy.force const_fp_ob in
      let m = Method.scale_time m !Params.timeout_stretch in
        (* retrieve results from fingerprints file *)
      let (to_do, to_print) = already_processed ob m in
      assert ((List.length to_print) <= 1);
        (* some method succeeded in proving ? *)
      let has_success = List.exists is_success to_print in
      let with_enabled_and_fp =
          if (to_do = None) && (not has_success) && expand_enabled then
            begin match List.hd to_print with
            | NTriv ((RFail r), m) ->
                let (normalize_expand_ob, _) = Lazy.force p in
                let ob = normalize_expand_ob in
                let ob = invert_renaming ob in
                let res = List.hd to_print in
                Toolbox.print_old_res ob res true;
                true
            | NTriv (RInt, m) -> false
            | NTriv (RSucc, m) -> assert false
            | Triv -> assert false
            end
          else false
        in
      (* attempting to prove, or noting that proof obligation is trivial *)
      if has_success then begin
        List.iter (fun st -> Toolbox.print_old_res ob st false) to_print;
        record true ob;
        Schedule.Immediate true
      end else begin
        let (p1, expand_success) = Lazy.force p in
        let normalize_expand_ob = lazy p1 in
        (* Note: triviality check must be done after expanding definitions *)
        let trivial_ob =
            try
                lazy (trivial (Lazy.force normalize_expand_ob))
            with Failure msg ->
                lazy (trivial (Lazy.force const_fp_ob))
            in
        let result = begin
            try
                if is_trivial trivial_ob then begin
                    save_result fpout thyout record (Lazy.force trivial_ob);
                    Some (Schedule.Immediate true)
                end else begin
                    None
                end
            with Failure msg ->
                begin
                record false ob;
                Some (Schedule.Immediate false)
                end
            end
        in
        match result with
        | Some schedule -> schedule  (* is trivial *)
        | None -> (* nontrivial *)
      begin
        if not with_enabled_and_fp then
            List.iter (fun st -> Toolbox.print_old_res ob st true) to_print;
        if to_print <> [] then record has_success ob;
        assert (to_do <> Some Method.ExpandENABLED);
        assert (to_do <> Some Method.ExpandCdot);
        assert (to_do <> Some Method.AutoUSE);
        assert (to_do <> Some Method.Lambdify);
        assert (to_do <> Some Method.ENABLEDaxioms);
        assert (to_do <> Some Method.LevelComparison);
        (* try backends only if any expansions of `ENABLED` and `\cdot` that
        have been requested have been completed successfully.
        *)
        if expand_success then
        begin
        match to_do with
        | None -> Schedule.Immediate has_success
        | Some meth ->
           let frontend_ob =
             match meth with
             (* The obligations sent to FOL backends are normalized using the
              * action frontend by default *)
             | Method.LS4 _ ->
                 lazy (Pltl.process_obligation
                           (Lazy.force normalize_expand_ob))
             | _ ->
                 lazy (Action.process_obligation
                           (Lazy.force normalize_expand_ob))
           in
           let tmo = !Params.backend_timeout *. !Params.timeout_stretch in
           print_obl_and_msg
               (Lazy.force frontend_ob)
               "Front-end returns the proof obligation:\n";
            (*
             assert ((not (
                 Expr.Eq.expr (Lazy.force normalize_expand_ob).obl.core.active
                                (noprops (Internal FALSE)) ))
                || (
                    Expr.Eq.expr (Lazy.force frontend_ob).obl.core.active
                                (noprops (Internal FALSE)) ) );
            *)
            let f () = really_ship frontend_ob normalize_expand_ob meth
                                fpout thyout record
            (* let f () = Schedule.Immediate false *)
           in
           begin
           match Util.run_with_timeout tmo f () with
           | Some result -> result
           | None ->
                 let msg =
                    "\n\\* internal timeout while processing obligation\n" in
                 let res =
                    NTriv (RFail (Some (Cantwork "internal timeout")), m) in
                 Toolbox.print_new_res ob res msg (Some tmo);
                 record false ob;
                 Schedule.Immediate false
            end
        end else Schedule.Immediate false
      end
      end
    in
    List.map (fun x -> fun () -> prep_meth x) meths
  with Failure msg -> []
  end
;;

let make_task fpout thyout record ob =
  match ob.id with
  | None -> (* FIXME I think this case is impossible -DD *)
     let msg =
       "Obligation (see below) contains forms not supported by Isabelle/TLA+"
     in
     let pr_obl ff =
       ignore (Expr.Fmt.pp_print_sequent (Deque.empty, Ctx.dot) ff ob.obl.core)
     in
     Util.eprintf ~at:ob.obl "%s@\n  @[<b0>%t@]@." msg pr_obl;
     (0, [])
  | Some id -> (id, ship ob fpout thyout record)
;;
