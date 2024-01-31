(*  Copyright 2004 INRIA  *)

open Expr;;
open Llproof;;
open Namespace;;
open Printf;;

let ( @@ ) = List.rev_append;;

type coqterm =
  | Cvar of string
  | Cty of string
  | Clam of string * coqterm * coqterm
  | Capp of coqterm * coqterm list
  | Cnot of coqterm
  | Cand of coqterm * coqterm
  | Cor of coqterm * coqterm
  | Cimply of coqterm * coqterm
  | Cequiv of coqterm * coqterm
  | Call of string * string * coqterm
  | Cex of string * string * coqterm
  | Clet of string * coqterm * coqterm
  | Cwild
  | Cmatch of coqterm * (string * string list * coqterm) list
  | Cifthenelse of coqterm * coqterm * coqterm
  | Cfix of string * string * coqterm
  | Cannot of coqterm * coqterm
;;

type coqproof =
  Phrase.phrase list * (string * coqterm) list * string * coqterm
;;

let lemma_env = (Hashtbl.create 97 : (string, string list) Hashtbl.t);;


let mapping = ref [];;
let constants_used = ref [];;

let rawname e = sprintf "%s%x" hyp_prefix (Index.get_number e);;

let rec make_mapping phrases =
  match phrases with
  | [] -> []
  | Phrase.Hyp (n, e, _) :: t -> (rawname e, n) :: (make_mapping t)
  | Phrase.Def _ :: t -> make_mapping t
  | Phrase.Sig _ :: t -> make_mapping t
  | Phrase.Inductive _ :: t -> make_mapping t
;;

let init_mapping phrases =
  mapping := make_mapping phrases;
  constants_used := [];
;;

let getname e =
  let result = rawname e in
  try List.assoc result !mapping
  with Not_found -> result
;;

let is_mapped e = List.mem_assoc (rawname e) !mapping;;

let is_goal e =
  try List.assoc (rawname e) !mapping = goal_name
  with Not_found -> false
;;

let induct_map = ref [];;
let constructor_table = (Hashtbl.create 100 : (string, unit) Hashtbl.t);;

let init_induct phrases =
  induct_map := [];
  Hashtbl.clear constructor_table;
  let add_induct p =
    match p with
    | Phrase.Inductive (name, args, cons, schema) ->
       induct_map := (name, (args, cons, schema)) :: !induct_map;
       List.iter (fun (c, _) -> Hashtbl.add constructor_table c ()) cons;
    | Phrase.Hyp _ | Phrase.Def _ | Phrase.Sig _ -> ()
  in
  List.iter add_induct phrases;
;;

let get_induct name =
  try List.assoc name !induct_map
  with Not_found -> assert false
;;

let is_constr e =
  match e with
  | Eapp ("@", Evar (f, _) :: _, _) -> Hashtbl.mem constructor_table f
  | Eapp (f, _, _) -> Hashtbl.mem constructor_table f
  | _ -> false
;;


exception Cannot_infer of string;;

(* For now, [synthesize] is very simple-minded. *)
let synthesize s =
  let ty = Mltoll.get_meta_type s in
  match ty with
  | "" -> any_name (* FIXME all_list should get the types from context *)
  | t when t = univ_name -> any_name
  | "nat" -> "O"
  | "bool" -> "true"
  | "Z" -> "Z0"
  | t when is_mapped (evar t) ->
      let result = getname (evar t) in
      constants_used := result :: !constants_used;
      result
  | _ -> raise (Cannot_infer ty)
;;

let to_var e =
  match e with
  | Evar (v, _) -> v
  | _ -> assert false
;;

let cty s =
  match s with
  | "" -> Cwild
  | _ -> Cty s
;;

let rec trexpr env e =
  match e with
  | Evar (v, _) when Mltoll.is_meta v && not (List.mem v env) ->
      Cvar (synthesize v)
  | Evar (v, _) -> Cvar v
  | Emeta _ -> assert false
  | Eapp ("$match", e1 :: cases, _) ->
      Cmatch (trexpr env e1, List.map (trcase env []) cases)
  | Eapp ("$fix", Elam (Evar (f, _), ty, e1, _) :: args, _) ->
      Capp (Cfix (f, ty, trexpr env e1), List.map (trexpr env) args)
  | Eapp ("FOCAL.ifthenelse", [e1; e2; e3], _) ->
      Cifthenelse (trexpr env e1, trexpr env e2, trexpr env e3)
  | Eapp ("$string", [Evar (v, _)], _) -> Cvar v
  | Eapp (f, args, _) -> Capp (Cvar f, List.map (trexpr env) args)
  | Enot (e1, _) -> Cnot (trexpr env e1)
  | Eand (e1, e2, _) -> Cand (trexpr env e1, trexpr env e2)
  | Eor (e1, e2, _) -> Cor (trexpr env e1, trexpr env e2)
  | Eimply (e1, e2, _) -> Cimply (trexpr env e1, trexpr env e2)
  | Eequiv (e1, e2, _) -> Cequiv (trexpr env e1, trexpr env e2)
  | Etrue -> Cvar "True"
  | Efalse -> Cvar "False"
  | Eall (Evar (v, _), t, e1, _) -> Call (v, t, trexpr (v::env) e1)
  | Eall _ -> assert false
  | Eex (Evar (v, _), t, e1, _) -> Cex (v, t, trexpr (v::env) e1)
  | Eex _ -> assert false
  | Etau _ -> Cvar (Index.make_tau_name e)
  | Elam (Evar (v, _), t, e1, _) -> Clam (v, cty t, trexpr (v::env) e1)
  | Elam _ -> assert false

and trcase env accu e =
  match e with
  | Eapp ("$match-case", [Evar (constr, _); body], _) ->
     (constr, List.rev accu, trexpr env body)
  | Elam (Evar (v, _), _, body, _) -> trcase env (v :: accu) body
  | _ -> assert false
;;

(*
let getv env e = Cannot (Cvar (getname e), trexpr env e);;
*)
let getv env e = Cvar (getname e);;

let tropt env e = if !Globals.short_flag then Cwild else trexpr env e;;
let trpred env v ty p = Clam (v, cty ty, trexpr env p);;

let mklam env v t = Clam (getname v, tropt env v, t);;
let mklams env args t = List.fold_right (mklam env) args t;;

let mkfixcase (c, args) =
  let mklam e arg =
    match arg with
    | Phrase.Self -> Clam ("_", Cwild, Clam ("_", Cwild, e))
    | Phrase.Param _ -> Clam ("_", Cwild, e)
  in
  List.fold_left mklam (Clam ("x", Cwild, Cvar "x")) args
;;

let rec mk_eq_args gen pre post1 post2 =
  match post1, post2 with
  | [], [] -> []
  | h1 :: t1, h2 :: t2 ->
     let args x = List.rev_append pre (x :: t1) in
     let ctx x = gen (args x) in
     (ctx, h1, h2) :: mk_eq_args gen (h2 :: pre) t1 t2
  | _ -> assert false
;;

let rec trtree env node =
  let {conc = conc; rule = rule; hyps = hyps} = node in
  let trexpr = trexpr env in
  let tropt = tropt env in
  let trpred = trpred env in
  let mklam = mklam env in
  let tr_subtree_1 = tr_subtree_1 env in
  let tr_subtree_2 = tr_subtree_2 env in
  match rule with
  | Rfalse -> getv env (efalse)
  | Rnottrue -> Capp (Cvar "zenon_nottrue", [getv env (enot (etrue))])
  | Raxiom (p) -> Capp (getv env (enot p), [getv env p])
  | Rcut (p) ->
      let (subp, subnp) = tr_subtree_2 hyps in
      let lamp = mklam p subp in
      Clet (getname (enot p), lamp, subnp)
  | Rnoteq (e) ->
      let e_neq_e = getv env (enot (eapp ("=", [e; e]))) in
      Capp (Cvar "zenon_noteq", [Cwild; trexpr e; e_neq_e])
  | Reqsym (e, f) ->
      let e_eq_f = getv env (eapp ("=", [e; f])) in
      let f_neq_e = getv env (enot (eapp ("=", [f; e]))) in
      Capp (Cvar "zenon_eqsym", [Cwild; trexpr e; trexpr f; e_eq_f; f_neq_e])
  | Rnotnot (p) ->
      let sub = mklam p (tr_subtree_1 hyps) in
      Capp (getv env (enot (enot p)), [sub])
  | Rconnect (And, p, q) ->
      let sub = mklam p (mklam q (tr_subtree_1 hyps)) in
      Capp (Cvar "zenon_and", [tropt p; tropt q; sub; getv env (eand (p, q))])
  | Rconnect (Or, p, q) ->
      let (subp, subq) = tr_subtree_2 hyps in
      let lamp = mklam p subp in
      let lamq = mklam q subq in
      let concl = getv env (eor (p, q)) in
      Capp (Cvar "zenon_or", [tropt p; tropt q; lamp; lamq; concl])
  | Rconnect (Imply, p, q) ->
      let (subp, subq) = tr_subtree_2 hyps in
      let lamp = mklam (enot p) subp in
      let lamq = mklam q subq in
      let concl = getv env (eimply (p, q)) in
      Capp (Cvar "zenon_imply", [tropt p; tropt q; lamp; lamq; concl])
  | Rconnect (Equiv, p, q) ->
      let (sub1, sub2) = tr_subtree_2 hyps in
      let lam1 = mklam (enot p) (mklam (enot q) sub1) in
      let lam2 = mklam p (mklam q sub2) in
      let concl = getv env (eequiv (p, q)) in
      Capp (Cvar "zenon_equiv", [tropt p; tropt q; lam1; lam2; concl])
  | Rnotconnect (And, p, q) ->
      let (subp, subq) = tr_subtree_2 hyps in
      let lamp = mklam (enot p) subp in
      let lamq = mklam (enot q) subq in
      let concl = getv env (enot (eand (p, q))) in
      Capp (Cvar "zenon_notand", [tropt p; tropt q; lamp; lamq; concl])
  | Rnotconnect (Or, p, q) ->
      let sub = tr_subtree_1 hyps in
      let lam = mklam (enot p) (mklam (enot q) sub) in
      let concl = getv env (enot (eor (p, q))) in
      Capp (Cvar "zenon_notor", [tropt p; tropt q; lam; concl])
  | Rnotconnect (Imply, p, q) ->
      let sub = tr_subtree_1 hyps in
      let lam = mklam p (mklam (enot q) sub) in
      let concl = getv env (enot (eimply (p, q))) in
      Capp (Cvar "zenon_notimply", [tropt p; tropt q; lam; concl])
  | Rnotconnect (Equiv, p, q) ->
      let (sub1, sub2) = tr_subtree_2 hyps in
      let lam1 = mklam (enot p) (mklam q sub1) in
      let lam2 = mklam p (mklam (enot q) sub2) in
      let concl = getv env (enot (eequiv (p, q))) in
      Capp (Cvar "zenon_notequiv", [tropt p; tropt q; lam1; lam2; concl])
  | Rex (Eex (Evar (x, _) as vx, ty, px, _) as exp, z) ->
      let sub = tr_subtree_1 hyps in
      let zz = etau (vx, ty, px) in
      let zzn = Index.make_tau_name zz in
      let pzz = substitute [(vx, zz)] px in
      let lam = Clam (zzn, cty ty, mklam pzz sub) in
      Capp (Cvar "zenon_ex", [cty ty; trpred x ty px; lam; getv env exp])
  | Rex _ -> assert false
  | Rnotall (Eall (Evar (x, _) as vx, ty, px, _) as allp, z) ->
      let sub = tr_subtree_1 hyps in
      let zz = etau (vx, ty, enot (px)) in
      let zzn = Index.make_tau_name (zz) in
      let pzz = substitute [(vx, zz)] px in
      let lam = Clam (zzn, cty ty, mklam (enot (pzz)) sub) in
      let concl = getv env (enot allp) in
      Capp (Cvar "zenon_notall", [cty ty; trpred x ty px; lam; concl])
  | Rnotall _ -> assert false
  | Rall (Eall (Evar (x, _) as vx, ty, px, _) as allp, t) ->
      let sub = tr_subtree_1 hyps in
      let pt = substitute [(vx, t)] px in
      let lam = mklam pt sub in
      let p = trpred x ty px in
      let concl = getv env allp in
      Capp (Cvar "zenon_all", [cty ty; p; trexpr t; lam; concl])
  | Rall _ -> assert false
  | Rnotex (Eex (Evar (x, _) as vx, ty, px, _) as exp, t) ->
      let sub = tr_subtree_1 hyps in
      let npt = enot (substitute [(vx, t)] px) in
      let lam = mklam npt sub in
      let p = trpred x ty px in
      let concl = getv env (enot (exp)) in
      Capp (Cvar "zenon_notex", [cty ty; p; trexpr t; lam; concl])
  | Rnotex _ -> assert false
  | Rpnotp ((Eapp (p, args1, _) as pp),
            (Enot (Eapp (q, args2, _), _) as nqq)) ->
     assert (p = q);
     let args = mk_eq_args (fun x -> eapp (p, x)) [] args1 args2 in
     let base = getv env nqq in
     Capp (List.fold_right2 (mk_eq_node env) args hyps base, [getv env pp])
  | Rpnotp _ -> assert false
  | Rnotequal ((Eapp (f, args1, _) as ff), (Eapp (g, args2, _) as gg)) ->
     assert (f = g);
     let gen x = enot (eapp ("=", [eapp (f, x); gg])) in
     let args = mk_eq_args gen [] args1 args2 in
     let base = Capp (Cvar "zenon_notnot",
                      [Cwild; Capp (Cvar "refl_equal", [trexpr gg])])
     in
     let neq = enot (eapp ("=", [ff; gg])) in
     Capp (List.fold_right2 (mk_eq_node env) args hyps base, [getv env neq])
  | Rnotequal _ -> assert false
  | RcongruenceLR (p, a, b) ->
     let sub = tr_subtree_1 hyps in
     let h = apply p b in
     let lam = mklam h sub in
     let concl1 = getv env (apply p a) in
     let concl2 = getv env (eapp ("=", [a; b])) in
     Capp (Cvar "zenon_congruence_lr",
           [Cwild; trexpr p; trexpr a; trexpr b; lam; concl1; concl2])
  | RcongruenceRL (p, a, b) ->
     let sub = tr_subtree_1 hyps in
     let h = apply p b in
     let lam = mklam h sub in
     let concl1 = getv env (apply p a) in
     let concl2 = getv env (eapp ("=", [b; a])) in
     Capp (Cvar "zenon_congruence_rl",
           [Cwild; trexpr p; trexpr a; trexpr b; lam; concl1; concl2])
  | Rdefinition (name, sym, args, body, None, folded, unfolded) ->
      let sub = tr_subtree_1 hyps in
      Clet (getname unfolded, getv env folded, sub)
  | Rdefinition (name, sym, args, body, Some v, folded, unfolded) ->
      assert false (* TODO *)

(* FIXME should drop the coqterm translation or add yet another field
   to extensions *)
  | Rextension (_, "zenon_induct_discriminate",
                [], [Eapp ("=", [a; b], _) as e; car], []) ->
      Capp (Cvar "eq_ind", [trexpr a; trexpr car; Cvar "I"; trexpr b; getv env e])
  | Rextension (_, "zenon_induct_discriminate", _, _, _) -> assert false
  | Rextension (_, "zenon_induct_discriminate_diff",
                [], [a; b; car], []) ->
     let subp = tr_subtree_1 hyps in
     let h = enot (eapp ("=", [a; b])) in
     Clet (getname h, Capp (Cvar "eq_ind",
                            [trexpr a; trexpr car; Cvar "I"; trexpr b]),
           subp)
  | Rextension (_, "zenon_induct_discriminate_diff", _, _, _) -> assert false
  | Rextension (_, "zenon_induct_cases", [Evar (ty, _); ctx; e1], [c], hs) ->
     let (args, cstrs, schema) = get_induct ty in
     let typargs = List.map (fun _ -> Cwild) args in
     let make_hyp h (c, cargs) =
       let vars = List.map (fun x -> Expr.newname ()) cargs in
       let shape =
         let vvars = List.map evar vars in
         let params = List.map (fun _ -> evar "_") args in
         let base = enot (eapp ("=",
                                [e1; eapp ("@", evar c :: params @ vvars)]))
         in
         enot (all_list vvars base)
       in
       let sub = Capp (Cvar "NNPP", [Cwild; mklam shape (trtree env h)]) in
       let mkbody prf v = Capp (prf, [Cvar v]) in
       let body = List.fold_left mkbody sub vars in
       let abstract v arg body =
         match arg with
         | Phrase.Self -> Clam (v, Cwild, Clam ("_", Cwild, body))
         | Phrase.Param _ -> Clam (v, Cwild, body)
       in
       List.fold_right2 abstract vars cargs body
     in
     let recargs = List.map2 make_hyp hyps cstrs in
     let pred =
       let v = Expr.newvar () in
       trexpr (elam (v, "", enot (eapp ("=", [e1; v]))))
     in
     let refl = Capp (Cvar "refl_equal", [tropt e1]) in
     Capp (Cvar schema, typargs @ pred :: recargs @ tropt e1 :: [refl])
  | Rextension (_, "zenon_induct_cases", _, _, _) -> assert false
  | Rextension (_, "zenon_induct_induction_notall", [Evar (ty, _); p], [c], hs) ->
     let (args, _, schema) = get_induct ty in
     let typargs = List.map (fun _ -> Cwild) args in
     let mksub h prf =
       match h with
       | [h] -> Capp (Cvar "NNPP", [Cwild; mklam h (trtree env prf)])
       | _ -> assert false
     in
     let hypargs = List.map2 mksub hs hyps in
     let tp = trexpr p in
     let ap = Capp (Cvar schema, typargs @ tp :: hypargs) in
     let nap = getname c in
     Capp (Cvar nap, [ap])
  | Rextension (_, "zenon_induct_induction_notall", _, _, _) -> assert false
  | Rextension (_, "zenon_induct_fix", [Evar (ty, _); ctx; foldx; unfx; a],
                [c], [ [h] ]) ->
     let (args, cstrs, schema) = get_induct ty in
     let typargs = List.map (fun _ -> Cwild) args in
     let x = Expr.newvar () in
     let p = elam (x, "", eimply (eimply (apply ctx (apply unfx x), efalse),
                                  eimply (apply ctx (apply foldx x), efalse)))
     in
     let brs = List.map mkfixcase cstrs in
     let th = mklam h (tr_subtree_1 hyps) in
     Capp (Cvar schema, typargs @ trexpr p :: brs @ [trexpr a; th; getv env c])
  | Rextension (_, "zenon_induct_fix", _, _, _) -> assert false
  | Rextension (_, name, args, c, hs) ->
      let metargs = List.map trexpr args in
      let hypargs = List.map2 (mklams env) hs (List.map (trtree env) hyps) in
      let conargs = List.map (getv env) c in
      Capp (Cvar name, metargs @ hypargs @ conargs)
  | Rlemma (name, _) ->
      let args = Hashtbl.find lemma_env name in
      Capp (Cvar name, List.map (fun x -> trexpr (evar x)) args)

and tr_subtree_1 env l =
  match l with
  | [t] -> trtree env t
  | _ -> assert false

and tr_subtree_2 env l =
  match l with
  | [t1; t2] -> (trtree env t1, trtree env t2)
  | _ -> assert false

and mk_eq_node env (ctx, a, b) h sub =
  if Expr.equal a b then sub else begin
    let x = Expr.newname () in
    let c = Clam (x, Cwild, trexpr env (ctx (evar x))) in
    let aneb = enot (eapp ("=", [a; b])) in
    let thyp = mklam env aneb (trtree env h) in
    Capp (Cvar "zenon_subst",
          [Cwild; c; trexpr env a; trexpr env b; thyp; sub])
  end
;;

let rec make_lambdas l term =
  match l with
  | [] -> term
  | (ty, e) :: t -> Clam (e, ty, make_lambdas t term)
;;

let rec rm_lambdas l term =
  match l, term with
  | [], _ -> term
  | _ :: t, Clam (_, _, e) -> rm_lambdas t e
  | _, _ -> assert false
;;

let compare_hyps (name1, _) (name2, _) = Stdlib.compare name1 name2;;

let make_lemma { name = name; params = params; proof = proof } =
  let f (ty, e) =
    match e with
    | Evar (v, _) -> (ty, v)
    | Etau _ -> (ty, Index.make_tau_name e)
    | _ -> assert false
  in
  let rawparams = List.map f params in
  let pars = List.map (fun (ty, v) -> (cty ty, v)) rawparams in
  let parenv = List.map snd rawparams in
  let f x = is_goal x || not (is_mapped x) in
  let hyps = List.filter f proof.conc in
  let hyps0 = List.map (fun x -> (trexpr parenv x, getname x)) hyps in
  let hyps1 = List.sort compare_hyps hyps0 in
  let formals = pars @ hyps1 in
  let actuals = List.map snd formals in
  (make_lambdas formals (trtree parenv proof), name, actuals)
;;

let rec trp l =
  match l with
  | [th] ->
      let (thproof, thname, thargs) = make_lemma th
      in ([], rm_lambdas thargs thproof, thname, thargs)
  | h::t ->
      let (lem, name, args) = make_lemma h in
      Hashtbl.add lemma_env name args;
      let (lemmas, thproof, thname, thargs) = trp t in
      ((name, lem) :: lemmas, thproof, thname, thargs)
  | [] -> assert false
;;

let rec get_goal phrases =
  match phrases with
  | [] -> None
  | Phrase.Hyp (name, e, _) :: _ when name = goal_name -> Some e
  | _ :: t -> get_goal t
;;

let rec get_th_name lemmas =
  match lemmas with
  | [] -> assert false
  | [h] -> h.name
  | _ :: t -> get_th_name t
;;

let trproof phrases ppphrases l =
  try
    Hashtbl.clear lemma_env;
    init_mapping phrases;
    init_induct ppphrases;
    let (lemmas, raw, th_name, formals) = trp l in
    match get_goal phrases with
    | Some goal ->
        let trg = tropt [] goal in
        let term = Capp (Cvar "NNPP", [Cwild; Clam (goal_name, trg, raw)]) in
        ((phrases, lemmas, th_name, term), !constants_used)
    | None -> ((phrases, lemmas, th_name, raw), !constants_used)
  with
  | Cannot_infer ty ->
      let msg = sprintf "cannot infer a value for a variable of type %s" ty in
      Error.err msg;
      raise Error.Abort
;;

(* ******************************************* *)

let line_len = 72;;

let rem_len = ref line_len;;
let buf = Buffer.create 100;;
exception Cut_before of int;;
exception Cut_at of int;;

let test_cut j c =
  match c with
  | '(' | ')' | '~' | '>' | ',' | '[' | ']' | '?' | '|' ->
      raise (Cut_before (j+1))
  | ':' | '<' -> raise (Cut_before j)
  | ' ' -> raise (Cut_at j)
  | _ -> ()
;;

let init_buf () = rem_len := line_len;;

let flush_buf oc =
  let s = Buffer.contents buf in
  let len = String.length s in
  let i = ref 0 in
  while !i + !rem_len <= len do
    try
      for j = !rem_len - 1 downto 1 do
        test_cut j s.[!i + j];
      done;
      if !rem_len < line_len then test_cut 0 s.[!i];
      for j = !rem_len to len - !i - 1 do
        test_cut j s.[!i + j];
      done;
      raise (Cut_before (len - !i))
    with
    | Cut_before j ->
        output_substring oc s !i j;
        i := !i + j;
        output_char oc '\n';
        rem_len := line_len;
    | Cut_at j ->
        output_substring oc s !i j;
        i := !i + j + 1;
        output_char oc '\n';
        rem_len := line_len;
  done;
  output_substring oc s !i (len - !i);
  rem_len := !rem_len - (len - !i);
  Buffer.clear buf;
;;

let rec get_lams accu t =
  match t with
  | Clam (s, ty, t1) -> get_lams ((s, ty) :: accu) t1
  | _ -> (List.rev accu, t)
;;

let make_lemma_type t =
  let (tys, _) = get_lams [] t in
  let make_funtype (v, ty1) ty2 =
    match ty1 with
    | Cty ty -> Call (v, ty, ty2)
    | Cwild -> Call (v, "", ty2)
    | _ -> Cimply (ty1, ty2)
  in
  List.fold_right make_funtype tys (cty "False")
;;

(* ******************************************* *)

let tr_ty t =
  match t with
  | t when t = univ_name -> t
  | "" -> assert false
  | s -> sprintf "%s" s
;;

let pr_oc oc prefix t =
  let rec pr_list p b l =
    let f t = bprintf b " %a" p t; in
    List.iter f l;
  in
  let pr_comma_list p b l =
    let f t = bprintf b ",%a" p t; in
    match l with
    | [] -> assert false
    | h::t ->
       p b h;
       List.iter f t;
  in
  let pr_id b x = bprintf b "%s" x;
  in
  let pr_ty b t = bprintf b "%s" (tr_ty t);
  in
  let rec pr b t =
    match t with
    | Cvar "" -> assert false
    | Cvar s -> bprintf b "%s" s; flush_buf oc;
    | Cty s -> bprintf b "%a" pr_ty s;
    | Clam (_, _, Clam _) ->
        let (lams, body) = get_lams [] t in
        bprintf b "(fun%a=>%a)" pr_lams lams pr body;
    | Clam (s, Cwild, t2) -> bprintf b "(fun %s=>%a)" s pr t2;
    | Clam (s, t1, t2) -> bprintf b "(fun %s:%a=>%a)" s pr t1 pr t2;
    | Capp (Cvar "=", [e1; e2]) ->
       bprintf b "(%a = %a)" pr e1 pr e2;  (* NOTE: spaces are needed *)
    | Capp (Cvar "%", [e1; e2]) ->
       bprintf b "(%a)%%%a" pr e1 pr e2
    | Capp (Cvar "=", args) -> bprintf b "(@eq _%a)" (pr_list pr) args;
    | Capp (t1, []) -> pr b t1;
    | Capp (Capp (t1, args1), args2) -> pr b (Capp (t1, args1 @ args2));
    | Capp (t1, args) -> bprintf b "(%a%a)" pr t1 (pr_list pr) args;
    | Cnot (t1) -> bprintf b "(~%a)" pr t1;
    | Cand (t1,t2) -> bprintf b "(%a/\\%a)" pr t1 pr t2;
    | Cor (t1,t2) -> bprintf b "(%a\\/%a)" pr t1 pr t2;
    | Cimply (t1, t2) -> bprintf b "(%a->%a)" pr t1 pr t2;
    | Cequiv (t1, t2) -> bprintf b "(%a<->%a)" pr t1 pr t2;
    | Call (v, "", t1) -> bprintf b "(forall %s,%a)" v pr t1;
    | Call (v, ty, t1) -> bprintf b "(forall %s:%a,%a)" v pr_ty ty pr t1;
    | Cex (v, "", t1) -> bprintf b "(exists %s,%a)" v pr t1;
    | Cex (v, ty, t1) -> bprintf b "(exists %s:%a,%a)" v pr_ty ty pr t1;
    | Clet (v, t1, t2) -> bprintf b "(let %s:=%a in %a)" v pr t1 pr t2;
    | Cwild -> bprintf b "_";
    | Cmatch (e, cl) -> bprintf b "match %a with%a end" pr e pr_cases cl;
    | Cfix (f, ty, e1) ->
       let (lams, body) = get_lams [] e1 in
       bprintf b "(fix %s %a:%a:=%a)" f pr_lams lams pr_ty ty pr body
    | Cifthenelse (e1, e2, e3) ->
       bprintf b "(if %a then %a else %a)" pr e1 pr e2 pr e3;
    | Cannot (e1, e2) ->
       bprintf b "(%a:%a)" pr e1 pr e2;

  and pr_lams b l =
    let f (v, ty) =
      match ty with
      | Cwild -> bprintf b " %s" v;
      | _ -> bprintf b "(%s:%a)" v pr ty;
    in
    List.iter f l;

  and pr_cases b l =
    let f case =
      match case with
      | (constr, args, rhs) when constr = tuple_name ->
         bprintf b "|(%a)=>%a" (pr_comma_list pr_id) args pr rhs;
      | (constr, args, rhs) ->
         bprintf b "|%s%a=>%a" constr (pr_list pr_id) args pr rhs;
    in
    List.iter f l;

  in

  init_buf ();
  bprintf buf "%s" prefix;
  pr buf t;
  flush_buf oc;
;;

let print_lemma oc (name, t) =
  let prefix = sprintf "let %s:" name in
  pr_oc oc prefix (make_lemma_type t);
  fprintf oc ":=\n";
  pr_oc oc "" t;
  fprintf oc "in\n";
;;

let use_hyp oc count p =
  match p with
  | Phrase.Hyp (name, _, _) when name = goal_name -> count
  | Phrase.Hyp (name, _, _)
  | Phrase.Def (DefReal (name, _, _, _, _))
  -> fprintf oc "assert (%s%d := %s).\n" dummy_prefix count name;
     count + 1
  | _ -> count
;;

let print_use_all oc phrases =
  if !Globals.use_all_flag then ignore (List.fold_left (use_hyp oc) 0 phrases);
;;

let print_theorem oc lemmas (name, t) phrases =
  let prefix = sprintf "Theorem %s:" name in
  begin match get_goal phrases with
  | Some (Enot (g, _)) -> pr_oc oc prefix (trexpr [] g);
  | None -> pr_oc oc prefix (trexpr [] efalse);
  | _ -> assert false
  end;
  fprintf oc ".\nProof.\n";
  print_use_all oc phrases;
  fprintf oc "exact(\n";
  List.iter (print_lemma oc) lemmas;
  pr_oc oc "" t;
  fprintf oc ").\nQed.\n";
;;

type result =
  | Prop
  | Term
  | Type of string
  | Indirect of string
;;
type signature =
  | Default of int * result
  | Declared of string
  | Hyp_name
;;

let predefined = [
  "Type"; "Prop"; "Set"; "nat"; "="; "$match"; "$match-case"; "$fix";
];;

let is_nat s =
  try
    for i = 0 to String.length s - 1 do
      if not (Misc.isdigit s.[i]) then raise Exit;
    done;
    true
  with Exit -> false
;;

let get_signatures ps ext_decl =
  let symtbl = (Hashtbl.create 97 : (string, signature) Hashtbl.t) in
  let defined = ref (predefined @@ ext_decl) in
  let add_sig sym arity kind =
    if not (Hashtbl.mem symtbl sym) then
      Hashtbl.add symtbl sym (Default (arity, kind))
  in
  let rec get_sig r env e =
    match e with
    | Evar ("_", _) -> ()
    | Evar (s, _) when is_nat s -> ()
    | Evar (s, _) -> if not (List.mem s env) then add_sig s 0 r;
    | Emeta _ | Etrue | Efalse -> ()
    | Eapp (s, args, _) ->
        add_sig s (List.length args) r;
        List.iter (get_sig Term env) args;
    | Eand (e1, e2, _) | Eor (e1, e2, _)
    | Eimply (e1, e2, _) | Eequiv (e1, e2, _)
      -> get_sig Prop env e1;
         get_sig Prop env e2;
    | Enot (e1, _) -> get_sig Prop env e1;
    | Eall (Evar (v, _), _, e1, _) | Eex (Evar (v, _), _, e1, _)
    | Etau (Evar (v, _), _, e1, _) | Elam (Evar (v, _), _, e1, _)
      -> get_sig Prop (v::env) e1;
    | Eall _ | Eex _ | Etau _ | Elam _ -> assert false
  in
  let set_type sym typ =
    Hashtbl.remove symtbl sym;
    Hashtbl.add symtbl sym typ;
  in
  let do_phrase p =
    match p with
    | Phrase.Hyp (name, e, _) ->
        get_sig Prop [] e;
        set_type name Hyp_name;
    | Phrase.Def (DefReal (_, s, _, e, _)) ->
        defined := s :: !defined;
        get_sig (Indirect s) [] e;
    | Phrase.Def (DefRec (eqn, s, _, e)) ->
        defined := s :: !defined;
        get_sig (Indirect s) [] e;
    | Phrase.Def (DefPseudo _) -> assert false
    | Phrase.Sig (sym, args, res) ->
        set_type sym (Declared res);
    | Phrase.Inductive (ty, args, constrs, schema) ->
        set_type ty (Declared "Type");  (* FIXME add arguments *)
        List.iter (fun (x, _) -> set_type x (Declared ty)) constrs;
  in
  List.iter do_phrase ps;
  let rec follow_indirect path s =
    if List.mem s path then Prop else
      begin try
        match Hashtbl.find symtbl s with
        | Default (_, ((Prop|Term|Type _) as kind)) -> kind
        | Default (_, Indirect s1) -> follow_indirect (s::path) s1
        | Declared (res) -> Type res
        | Hyp_name -> assert false
      with Not_found -> Prop
      end
  in
  let find_sig sym sign l =
    if List.mem sym !defined then l
    else begin
      match sign with
      | Default (arity, (Prop|Term|Type _)) -> (sym, sign) :: l
      | Default (arity, Indirect s) ->
          (sym, Default (arity, follow_indirect [] s)) :: l
      | Declared (res) -> l
      | Hyp_name -> l
    end
  in
  Hashtbl.fold find_sig symtbl []
;;

let print_signature oc (sym, sign) =
  let rec print_arity n =
    if n = 0 then () else begin
      fprintf oc "%s -> " univ_name;
      print_arity (n-1);
    end;
  in
  fprintf oc "Parameter %s : " sym;
  match sign with
  | Default (arity, kind) ->
      begin
        print_arity arity;
        match kind with
        | Prop -> fprintf oc "Prop.\n";
        | Term -> fprintf oc "%s.\n" univ_name;
        | Type s -> fprintf oc "%s.\n" s;
        | Indirect _ -> assert false;
      end;
  | Declared (res) -> assert false
  | Hyp_name -> assert false
;;

let print_var oc e =
  match e with
  | Evar (s, _) -> fprintf oc " %s" s;
  | _ -> assert false
;;

let print_constr oc tyname args (cname, tys) =
  let print_ty t =
    match t with
    | Phrase.Param s -> fprintf oc "%s -> " s;
    | Phrase.Self ->
       fprintf oc "%s" tyname;
       List.iter (fprintf oc " %s") args;
       fprintf oc " -> ";
  in
  fprintf oc " | %s : " cname;
  List.iter print_ty tys;
  fprintf oc "%s\n" tyname;
;;

let declare_hyp oc h =
  match h with
  | Phrase.Hyp (name, _, _) when name = goal_name -> ()
  | Phrase.Hyp (name, stmt, _) ->
      pr_oc oc (sprintf "Parameter %s : " name) (trexpr [] stmt);
      fprintf oc ".\n";
  | Phrase.Def (DefReal (name, sym, [], body, None)) ->
      let prefix = sprintf "Definition %s := " sym in
      pr_oc oc prefix (trexpr [] body);
      fprintf oc ".\n";
  | Phrase.Def (DefReal (name, sym, params, body, None)) ->
      fprintf oc "Definition %s := fun" sym;
      List.iter (print_var oc) params;
      fprintf oc " =>\n";
      pr_oc oc "" (trexpr [] body);
      fprintf oc ".\n";
  | Phrase.Def (DefReal (name, sym, params, body, Some v)) ->
      fprintf oc "Fixpoint %s" sym;
      List.iter (print_var oc) params;
      fprintf oc " { struct %s } :=\n" v;
      pr_oc oc "" (trexpr [] body);
      fprintf oc ".\n";
  | Phrase.Def _ -> assert false
  | Phrase.Sig (sym, args, res) ->
      fprintf oc "Parameter %s : " sym;
      List.iter (fun x -> fprintf oc "%s -> " (tr_ty x)) args;
      fprintf oc "%s.\n" (tr_ty res);
  | Phrase.Inductive (name, args, constrs, schema) ->
      fprintf oc "Inductive %s" name;
      List.iter (fprintf oc " %s") args;
      fprintf oc " : Type :=\n";
      List.iter (print_constr oc name args) constrs;
      fprintf oc " (* %s *)" schema;
      fprintf oc ".\n";
;;

let declare_context oc phrases =
  if not !Globals.quiet_flag then fprintf oc "(* BEGIN-CONTEXT *)\n";
  fprintf oc "Add LoadPath \"%s\".\n" !Globals.load_path;
  fprintf oc "Require Import zenon.\n";
  Extension.declare_context_coq oc;
  let ext_decl = Extension.predef () in
  fprintf oc "Parameter %s : Set.\n" univ_name;
  fprintf oc "Parameter %s : %s.\n" any_name univ_name;
  let sigs = get_signatures phrases ext_decl in
  List.iter (print_signature oc) sigs;
  List.iter (declare_hyp oc) phrases;
  if not !Globals.quiet_flag then fprintf oc "(* END-CONTEXT *)\n";
  flush oc;
;;

let print oc (phrases, lemmas, thname, thproof) =
  if !Globals.ctx_flag then declare_context oc phrases;
  if not !Globals.quiet_flag then fprintf oc "(* BEGIN-PROOF *)\n";
  print_theorem oc lemmas (thname, thproof) phrases;
  if not !Globals.quiet_flag then fprintf oc "(* END-PROOF *)\n";
;;
