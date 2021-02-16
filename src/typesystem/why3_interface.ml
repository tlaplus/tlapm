(************************************************************************
*
*  why3_interface.ml
*  
*
*  Created by Hernán Vanzetto on 
*  Copyright (c) 2013 __MyCompanyName__. All rights reserved.
*
************************************************************************)

open Ext
open Property

open Expr.T
open Printf
open List

open Smtcommons
module B = Builtin
(* open Typ_t *)

module T = Typ_t
module SMap = Map.Make (String)


(* open Why3 *)
(* open Format *)
module Whyconf = Why3.Whyconf
module Env = Why3.Env
module Driver = Why3.Driver
module Exn_printer = Why3.Exn_printer
module WhyFormat = Format
module Task = Why3.Task
module Decl = Why3.Decl
module Pretty = Why3.Pretty
module Call_provers = Why3.Call_provers
module Tm = Why3.Term
module Th = Why3.Theory
module Ty = Why3.Ty
module Ident = Why3.Ident
module Number = Why3.Number

  let config : Whyconf.config = Whyconf.read_config None

  (* the [main] section of the config file *)
  let main : Whyconf.main = Whyconf.get_main config

  (* all the provers detected, from the config file *)
  (* let provers : Whyconf.config_prover Whyconf.Mprover.t =
    Whyconf.get_provers config in *)
    
  (* One prover named Alt-Ergo in the config file *)
  let alt_ergo : Whyconf.config_prover =
    let fp = Whyconf.parse_filter_prover "Alt-Ergo" in
    (** all provers that have the name "Alt-Ergo" *)
    let provers = Whyconf.filter_provers config fp in
    if Whyconf.Mprover.is_empty provers then begin
      eprintf "Prover Alt-Ergo not installed or not configured@.";
      exit 0
    end else
      snd (Whyconf.Mprover.max_binding provers)
  ;;

  (* builds the environment from the [loadpath] *)
  let env : Env.env = Env.create_env (Whyconf.loadpath main)

  (* loading the Alt-Ergo driver *)
  let alt_ergo_driver : Driver.driver =
    try
      Driver.load_driver env alt_ergo.Whyconf.driver []
    with e ->
      WhyFormat.eprintf "Failed to load driver for alt-ergo: %a@."
        Exn_printer.exn_printer e;
      exit 1
  ;;
  
  let int_theory : Th.theory = Env.find_theory env ["int"] "Int"
  (* let str_theory : Th.theory = Env.find_theory env ["string"] "String" *)

let th_find_ls = Th.ns_find_ls int_theory.Th.th_export;;

let plus_symbol : Tm.lsymbol  = th_find_ls ["infix +"]
let minus_symbol : Tm.lsymbol = th_find_ls ["infix -"]
let mult_symbol : Tm.lsymbol  = th_find_ls ["infix *"]
(* let exp_symbol : Tm.lsymbol   = th_find_ls ["infix ^"] *)
(* let uminus_symbol : Tm.lsymbol = th_find_ls ["-"] *)
let lt_symbol : Tm.lsymbol    = th_find_ls ["infix <"]
let lteq_symbol : Tm.lsymbol  = th_find_ls ["infix <="]
let gt_symbol : Tm.lsymbol    = th_find_ls ["infix >"]
let gteq_symbol : Tm.lsymbol  = th_find_ls ["infix >="]

let sort_u = Ty.ty_var (Ty.create_tvsymbol (Ident.id_fresh ("u")))
let sort_str = Ty.ty_var (Ty.create_tvsymbol (Ident.id_fresh "str"))

let mem_symbol : Tm.lsymbol = Tm.create_psymbol (Ident.id_fresh "mem") [sort_u ; sort_u]

let type_to_sort = function
  | T.Int -> Ty.ty_int
  | T.Bool -> Ty.ty_bool
  | T.Str -> sort_str
  | T.TyVar ([],a) -> sort_u
  | _ -> failwith "type_to_sort"

let create_vars id ts t (* : Tm.term  *)= 
  let ts = map type_to_sort ts in
  let t = type_to_sort t in
  match ts,t with
  | [], _ -> 
      let fsym = Tm.create_fsymbol (Ident.id_fresh id) [] t in
      (fsym,t,Tm.fs_app fsym [] t)
  (* | _, t' when Ty.ty_equal t' Ty.ty_bool -> 
      Tm.ps_app (Tm.create_psymbol (Ident.id_fresh id) ts) 
  | _, _ -> 
      Tm.create_fsymbol (Ident.id_fresh id) ts t *)
  | _ -> assert false

let var_terms = ref SMap.empty

let rec to_why cx e : Tm.term =
(* Util.eprintf "to_why: %a" (print_prop ()) (opaque cx e) ; *)
  let tm_ix id = 
    begin try 
      let fsym,t,tm = SMap.find id !var_terms in
      tm
    with Not_found -> failwith "not a declared variable id" end
  in
  match e.core with
  | Ix n -> tm_ix (lookup_id cx n)
  | Opaque id -> tm_ix id
  (* | Apply ({ core = Ix n }, es) -> 
      let es = map (to_why cx) es in
      proc_id_es cx e es *)
  (* | Apply ({ core = Opaque id }, es) ->  *)
  (* | FcnApp (f, es) -> *)
  (* | Dot (ex, h) -> *)
  | Apply ({core = Internal op}, es) -> 
      let es = map (to_why cx) es in
      begin match op, es with
      | B.Conj,      [e1 ; e2] -> Tm.t_and e1 e2
      | B.Disj,      [e1 ; e2] -> Tm.t_or e1 e2
      | B.Equiv,     [e1 ; e2] -> Tm.t_iff e1 e2
      | B.Eq,        [e1 ; e2] -> Tm.t_equ e1 e2
      | B.Implies,   [e1 ; e2] -> Tm.t_implies e1 e2
      | B.Neg,       [ex]      -> Tm.t_not ex
      | B.Mem,       [e1 ; e2] -> Tm.ps_app mem_symbol es
      (* | B.DOMAIN,    [f]       ->  *)

      | B.Plus,      [e1 ; e2] -> Tm.t_app_infer plus_symbol es
      | B.Minus,     [e1 ; e2] -> Tm.t_app_infer minus_symbol es
      | B.Times,     [e1 ; e2] -> Tm.t_app_infer mult_symbol es
      (* | B.Exp,       [e1 ; e2] -> Tm.t_app_infer exp_symbol es *)
      (* | B.Ratio,     [e1 ; e2]  *)
      | B.Lt,        [e1 ; e2] -> Tm.ps_app lt_symbol es
      | B.Lteq,      [e1 ; e2] -> Tm.ps_app lteq_symbol es
      | B.Gt,        [e1 ; e2] -> Tm.ps_app gt_symbol es
      | B.Gteq,      [e1 ; e2] -> Tm.ps_app gteq_symbol es
      (* | B.Quotient,  [e1 ; e2] ->  *)
      (* | B.Remainder, [e1 ; e2] ->  *)
      (* | B.Quotient,  [e1 ; e2] ->  *)
      (* | B.Remainder, [e1 ; e2] ->  *)
      (* | B.Range,     [e1 ; e2] ->  *)
      (* | B.Uminus,    [ex] -> Tm.t_app_infer uminus_symbol es *)
      
      (* | B.Seq,       [ex]     -> proc_op "Seq" es
      | B.Len,       [ex]     -> output (proc_op "Len" es)
      | B.SubSeq,    [ex;m;n] -> proc_op "SubSeq" es
      | B.Head,      [ex]     -> proc_op "Head" es
      | B.Tail,      [ex]     -> proc_op "Tail" es
      | B.BSeq,      [ex]     -> proc_op "BSeq" es
      | B.Cat,       [e1;e2]  -> proc_op "Cat" es
      | B.Append,    [e1;e2]  -> proc_op "Append" es
      | B.SelectSeq, [e1;e2]  -> proc_op "SelectSeq" es *)
      
      | _ -> 
          Errors.set (Internal op @@ e) "why_interface.ml: Arity mismatch";
          Util.eprintf ~at:(Internal op @@ e) "Arity mismatch" ;
          failwith "Backend.Smt.Smt.to_why"
      end
  (* | String s -> SMap.find s !string_terms *)
  | Internal B.TRUE  -> Tm.t_true
  | Internal B.FALSE -> Tm.t_false
  | List (And, es) -> Tm.t_and_simp_l (map (to_why cx) es)
  | List (Or, es)  -> Tm.t_or_simp_l (map (to_why cx) es)
  (* | Quant (q, ((_, _, No_domain) :: _ as bs), ex) -> *)
  (* | Quant (q, ((h, _, No_domain) :: _ as bs), ex) ->
      let var_x : Tm.vsymbol =
        Tm.create_vsymbol (Ident.id_fresh "x") Ty.ty_int 
      in
      Tm.t_forall_close [h.core] [(*triggers*)] (to_why cx ex) *)
  (* | SetEnum [] ->  *)
  (* | Record ses ->  *)
  (* | Tuple [] ->  *)
  (* | Tuple es -> *)
  | Num (n, "") -> Tm.t_const (Number.ConstInt (Number.int_const_dec n))
  (* | Internal B.Nat ->  *)
  (* | Internal B.Int ->  *)
  (* | Internal B.Infinity ->  *)
  | If (c, t, f) -> Tm.t_if (to_why cx c) (to_why cx t) (to_why cx f)
  | _ ->
      Util.eprintf ~at:e "SMT backend translation error.@\nWhy3 cannot process the expression: %a" (print_prop ()) e ;
      assert false
;;

let new_task fm (vs:Tm.lsymbol list) : Task.task = 
  let t = Task.use_export None int_theory in
  let t = fold_left Task.add_param_decl t vs in
  let goal_id1 : Decl.prsymbol = Decl.create_prsymbol (Ident.id_fresh "goal1") in
  Task.add_prop_decl t Decl.Pgoal goal_id1 fm
;;

(* let term_lsymbols env = SMap.mapi (fun x _ -> x) env *)

let rec normalize cx e = 
  match e.core with
  | Apply ({core = Internal B.Mem}, [x ; {core = SetEnum [y]}]) -> 
      let x = normalize cx x in
      let y = normalize cx y in
      (* map_exp normalize cx *) (Apply (Internal B.Eq |> noprops, [x;y]) |> noprops)
  | _ -> map_exp normalize cx e
  

let solve ((env:Typ_e.t),e) =
  var_terms := fold_left begin fun m (h,ot) -> 
    match ot with 
    | None -> m 
    | Some t -> SMap.add (hyp_name h) (create_vars (hyp_name h) [] t) m
    end SMap.empty (Typ_e.to_list env) ;
  (* let vs : string list = map (fun (x,_) -> x) env in   *)
  (* let vs = map (fun (x,_) -> x) env in   *)
  let vs = map (fun (x,(fsym,_,_)) -> fsym) (SMap.bindings !var_terms) in  
  let e = normalize [] e in
  let fm = to_why (Typ_e.to_cx env) e in
  (* Util.eprintf "@[   Why3 formula:@ %a@]@." Pretty.print_term fm ; *)
  let t = new_task fm vs in

  let call_prover t =
    Call_provers.wait_on_call
      (Driver.prove_task 
        ~command:alt_ergo.Whyconf.command
        ~timelimit:5 
        alt_ergo_driver t ()) ()
  in
  let r = call_prover t in
  if (r.Call_provers.pr_answer <> Valid) then begin
    (* Util.eprintf "@[   Decl:@ %a@]@." (Fmtutil.pp_print_delimited ~sep:Format.pp_print_cut Pretty.print_decl) (Task.task_decls t) ; *)
    ifprint 0 "  !!! @[<hov3>Decl:@ %a@]@." 
      (Fmtutil.pp_print_delimited ~sep:Format.pp_print_cut Pretty.print_decl) 
      (Task.local_decls t (Task.used_symbols (Task.used_theories t))) ;
    (* Util.eprintf "@[   Goal:@ %a@]@." Pretty.print_term (Task.task_goal_fmla t) ; *)
  end else () ;

  ifprint 1 "   @[<hov4>VC:@ %a@]" 
      (Fmtutil.pp_print_delimited ~sep:Format.pp_print_cut Pretty.print_decl) 
      (Task.local_decls t (Task.used_symbols (Task.used_theories t))) ;

  ifprint 1 "@[    ...alt-ergo answered %a in %5.3fs.@]" 
    Call_provers.print_prover_answer r.Call_provers.pr_answer
    r.Call_provers.pr_time ;

  Util.sprintf ?nonl:(Some ()) "%a" Call_provers.print_prover_answer r.Call_provers.pr_answer
;;  
  
