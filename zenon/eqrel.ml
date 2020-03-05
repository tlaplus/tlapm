(*  Copyright 2004 INRIA  *)

open Expr;;
open Mlproof;;

exception Wrong_shape;;

type direction = L | R;;

let symbol = ref None;;
let leaves = ref [];;
let typ = ref "";;

let rec check_pattern env sym e =
  match e with
  | Eapp (s, [(Evar _ as x); (Evar _ as y)], _)
  | Enot (Eapp (s, [(Evar _ as x); (Evar _ as y)], _), _)
    when s = sym ->
      if List.mem_assoc x env && List.mem_assoc y env then ()
      else raise Wrong_shape;
  | _ -> raise Wrong_shape;
;;

let get_skeleton e =
  match e with
  | Enot (Eapp (s, _, _), _) -> s
  | Eapp (s, _, _) -> s
  | _ -> raise Wrong_shape
;;

let get_type env e =
  match e with
  | Enot (Eapp (_, [Evar _ as x; _], _), _) -> List.assoc x env
  | Eapp (_, [Evar _ as x; _], _) -> List.assoc x env
  | _ -> assert false
;;

let do_leaf env e =
  match !symbol with
  | Some s ->
      check_pattern env s e;
      leaves := e :: !leaves;
  | None ->
      let s = get_skeleton e in
      check_pattern env s e;
      symbol := Some s;
      leaves := e :: !leaves;
      typ := get_type env e;
;;

let rec do_disj env e =
  match e with
  | Eor (e1, e2, _) -> do_disj env e1; do_disj env e2;
  | Eimply (e1, e2, _) -> do_disj env (enot e1); do_disj env e2;
  | Enot (Eand (e1, e2, _), _) -> do_disj env (enot e1); do_disj env (enot e2);
  | Enot (Enot (e1, _), _) -> do_disj env e1;
  | Enot (Etrue, _) | Efalse -> ()
  | _ -> do_leaf env e;
;;

let get_leaves path env e =
  symbol := None;
  leaves := [];
  typ := "";
  try
    do_disj env e;
    (List.rev path, env, !leaves, !typ)
  with Wrong_shape ->
    (List.rev path, env, [], "")
;;

let subexprs = ref [];;

let rec do_conj path env e =
  match e with
  | Eand (e1, e2, _) -> do_conj (L::path) env e1; do_conj (R::path) env e2;
  | Eall (v, t, e1, _) -> do_conj path ((v,t)::env) e1;
  | Enot (Eor (e1, e2, _), _) ->
      do_conj (L::path) env (enot e1); do_conj (R::path) env (enot e2);
  | Enot (Eimply (e1, e2, _), _) ->
      do_conj (L::path) env e1; do_conj (R::path) env (enot e2);
  | Enot (Eex (v, t, e1, _), _) -> do_conj path ((v,t)::env) (enot e1);
  | Enot (Enot (e1, _), _) -> do_conj path env e1;
  | Eequiv (e1, e2, _) ->
      do_conj (L::path) env (eimply (e1, e2));
      do_conj (R::path) env (eimply (e2, e1));
  | Enot (Eequiv (e1, e2, _), _) ->
      do_conj (L::path) env (eor (e1, e2));
      do_conj (R::path) env (eor (enot e1, enot e2));
  | _ -> subexprs := (get_leaves path env e) :: !subexprs;
;;

let get_subexprs e =
  subexprs := [];
  do_conj [] [] e;
  !subexprs
;;

let get_symbol l =
  match l with
  | Enot (Eapp (s, _, _), _) :: _ -> s
  | Eapp (s, _, _) :: _ -> s
  | _ -> assert false
;;

let rec partition pos neg l =
  match l with
  | [] -> (pos, neg)
  | (Enot _ as h) :: t -> partition pos (h::neg) t
  | h :: t -> partition (h::pos) neg t
;;

let rec number_var env v =
  match env with
  | (Evar (x, _), t) :: rest ->
      if x = v then List.length rest else number_var rest v
  | _ -> assert false
;;

let is_refl l e path env =
  match l with
  | [ Eapp (_, [Evar (x, _); Evar (y, _)], _) ] when x = y ->
     Some (e, path, [number_var env x])
  | _ -> None
;;

let is_sym l e path env =
  match partition [] [] l with
  | [ Eapp (_, [Evar (x1, _); Evar (y1, _)], _) ],
    [ Enot (Eapp (_, [Evar (x2, _); Evar (y2, _)], _), _) ]
    when x1 = y2 && y1 = x2 ->
      Some (e, path, List.map (number_var env) [x2; y2])
  | _ -> None
;;

let is_trans l e path env =
  match partition [] [] l with
  | [ Eapp (_, [Evar (x1, _); Evar (y1, _)], _) ],
    [ Enot (Eapp (_, [Evar (x2, _); Evar (y2, _)], _), _);
      Enot (Eapp (_, [Evar (x3, _); Evar (y3, _)], _), _)]
    when y2 = x3 && x1 = x2 && y1 = y3 ->
      Some (e, path, List.map (number_var env) [x1; y2; y1])
  | [ Eapp (_, [Evar (x1, _); Evar (y1, _)], _) ],
    [ Enot (Eapp (_, [Evar (x2, _); Evar (y2, _)], _), _);
      Enot (Eapp (_, [Evar (x3, _); Evar (y3, _)], _), _)]
    when y3 = x2 && x1 = x3 && y1 = y2 ->
      Some (e, path, List.map (number_var env) [x1; x2; y1])
  | _ -> None
;;

let is_transsym l e path env =
  match partition [] [] l with
  | [ Eapp (_, [Evar (x1, _); Evar (y1, _)], _) ],
    [ Enot (Eapp (_, [Evar (x2, _); Evar (y2, _)], _), _);
      Enot (Eapp (_, [Evar (x3, _); Evar (y3, _)], _), _)]
    when y2 = x3 && y1 = x2 && x1 = y3 ->
      Some (e, path, List.map (number_var env) [y1; y2; x1])
  | [ Eapp (_, [Evar (x1, _); Evar (y1, _)], _) ],
    [ Enot (Eapp (_, [Evar (x2, _); Evar (y2, _)], _), _);
      Enot (Eapp (_, [Evar (x3, _); Evar (y3, _)], _), _)]
    when y3 = x2 && y1 = x3 && x1 = y2 ->
      Some (e, path, List.map (number_var env) [y1; x2; x1])
  | _ -> None
;;

type info = {
  mutable refl : (Expr.expr * direction list * int list) option;
  mutable sym : (Expr.expr * direction list * int list) option;
  mutable trans : (Expr.expr * direction list * int list) option;
  mutable transsym : (Expr.expr * direction list * int list) option;
  mutable typ : string;
  mutable refl_hyp : Expr.expr option;
  mutable sym_hyp : Expr.expr option;
  mutable trans_hyp : Expr.expr option;
};;

let tbl = (Hashtbl.create 97 : (string, info) Hashtbl.t);;

let get_record s =
  try Hashtbl.find tbl s
  with Not_found ->
    let result = {refl = None; sym = None; trans = None;
                  transsym = None; typ = "";
                  refl_hyp = None; sym_hyp = None; trans_hyp = None}
    in
    Hashtbl.add tbl s result;
    result
;;

let analyse_subexpr e (path, env, sb, typ) =
  let refl = is_refl sb e path env in
  let sym = is_sym sb e path env in
  let trans = is_trans sb e path env in
  let transsym = is_transsym sb e path env in
  match refl, sym, trans, transsym with
  | None, None, None, None -> ()
  | _, _, _, _ ->
      let r = get_record (get_symbol sb) in
      if refl <> None then r.refl <- refl;
      if sym <> None then r.sym <- sym;
      if trans <> None then r.trans <- trans;
      if transsym <> None then r.transsym <- transsym;
      r.typ <- typ
;;

let analyse e = List.iter (analyse_subexpr e) (get_subexprs e);;

let subsumed_subexpr e (path, env, sb, typ) =
  if is_refl sb e path env <> None then
    (get_record (get_symbol sb)).refl <> None
  else if is_sym sb e path env <> None then
    (get_record (get_symbol sb)).sym <> None
  else if is_trans sb e path env <> None then
    (get_record (get_symbol sb)).trans <> None
  else if is_transsym sb e path env <> None then
    let r = get_record (get_symbol sb) in
    r.sym <> None && r.trans <> None
  else false
;;

let subsumed e = List.for_all (subsumed_subexpr e) (get_subexprs e);;

let eq_origin = Some (etrue, [], []);;
Hashtbl.add tbl "=" {
  refl = eq_origin;
  sym = eq_origin;
  trans = eq_origin;
  transsym = eq_origin;
  typ = "";
  refl_hyp = None;
  sym_hyp = None;
  trans_hyp = None;
};;

let refl s =
  try let r = Hashtbl.find tbl s in
      match r.refl with
      | None -> false
      | Some _ -> true
  with Not_found -> false
;;

let sym s =
  try let r = Hashtbl.find tbl s in
      match r.sym, r.refl, r.transsym with
      | Some _, _, _ -> true
      | _, Some _, Some _ -> true
      | _, _, _ -> false
  with Not_found -> false
;;

let trans s =
  try let r = Hashtbl.find tbl s in
      match r.trans, r.refl, r.transsym with
      | Some _, _, _ -> true
      | _, Some _, Some _ -> true
      | _, _, _ -> false
  with Not_found -> false
;;

let any s =
  try let r = Hashtbl.find tbl s in
      match r.refl, r.sym, r.trans with
      | None, None, None -> false
      | _, _, _ -> true
  with Not_found -> false
;;

type origin = Expr.expr * direction list * int list;;
type hyp_kind =
  | Refl of origin
  | Sym of origin
  | Sym2 of string * origin * origin   (* symbol, refl, transsym *)
  | Trans of origin
  | Trans2 of string * origin * origin (* symbol, refl, transsym *)
;;

module HE = Hashtbl.Make (Expr);;
let hyps_tbl =
  (HE.create 97 : hyp_kind HE.t)
;;

let get_refl_hyp s =
  assert (s <> "=");
  let r = Hashtbl.find tbl s in
  match r.refl_hyp with
  | Some e -> e
  | None ->
      let vx = evar "x" in
      let result = eall (vx, r.typ, eapp (s, [vx; vx])) in
      r.refl_hyp <- Some result;
      begin match r.refl with
      | Some (e, dirs, vars) -> HE.add hyps_tbl result (Refl ((e, dirs, vars)))
      | None -> assert false
      end;
      result
;;

let get_sym_hyp s =
  assert (s <> "=");
  let r = Hashtbl.find tbl s in
  match r.sym_hyp with
  | Some e -> e
  | None ->
      let vx = evar "x" and vy = evar "y" in
      let result = eall (vx, r.typ, eall (vy, r.typ,
                     eimply (eapp (s, [vx; vy]), eapp (s, [vy; vx]))))
      in
      r.sym_hyp <- Some result;
      begin match r.refl, r.sym, r.transsym with
      | _, Some (e, dirs, vars), _ ->
          HE.add hyps_tbl result (Sym ((e, dirs, vars)))
      | Some (e1, dir1, var1), _, Some (e2, dir2, var2) ->
          HE.add hyps_tbl result (Sym2 (s, (e1, dir1, var1), (e2, dir2, var2)))
      | _, _, _ -> assert false
      end;
      result
;;

let get_trans_hyp s =
  assert (s <> "=");
  let r = Hashtbl.find tbl s in
  match r.trans_hyp with
  | Some e -> e
  | None ->
      let vx = evar "x" and vy = evar "y" and vz = evar "z" in
      let result = eall (vx, r.typ, eall (vy, r.typ, eall (vz, r.typ,
                     eimply (eapp (s, [vx; vy]),
                       eimply (eapp (s, [vy; vz]), eapp (s, [vx; vz]))))))
      in
      r.trans_hyp <- Some result;
      begin match r.refl, r.trans, r.transsym with
      | _, Some (e, dirs, vars), _ ->
          HE.add hyps_tbl result (Trans ((e, dirs, vars)))
      | Some (e1, dir1, var1), _, Some (e2, dir2, var2) ->
          HE.add hyps_tbl result
                 (Trans2 (s, (e1, dir1, var1), (e2, dir2, var2)))
      | _, _, _ -> assert false
      end;
      result
;;

let inst_nall e =
  match e with
  | Enot (Eall (v, ty, f, _), _) ->
      let nf = enot f in
      let t = etau (v, ty, nf) in
      (Expr.substitute [(v, t)] nf, t)
  | _ -> assert false
;;

let rec decompose_disj e forms =
  match e with
  | Eor (e1, e2, _) ->
      let n1 = decompose_disj e1 forms in
      let n2 = decompose_disj e2 forms in
      make_node [e] (Or (e1, e2)) [[e1]; [e2]] [n1; n2]
  | Eimply (e1, e2, _) ->
      let ne1 = enot e1 in
      let n1 = decompose_disj ne1 forms in
      let n2 = decompose_disj e2 forms in
      make_node [e] (Impl (e1, e2)) [[ne1]; [e2]] [n1; n2]
  | Enot (Eand (e1, e2, _), _) ->
      let ne1 = enot e1 in
      let ne2 = enot e2 in
      let n1 = decompose_disj ne1 forms in
      let n2 = decompose_disj ne2 forms in
      make_node [e] (NotAnd (e1, e2)) [[ne1]; [ne2]] [n1; n2]
  | Enot (Enot (e1, _), _) ->
      let n1 = decompose_disj e1 forms in
      make_node [e] (NotNot (e1)) [[e1]] [n1]
  | Efalse -> make_node [e] False [] []
  | Enot (Etrue, _) -> make_node [e] NotTrue [] []
  | Eapp (s, _, _) ->
      let ne = enot e in
      assert (List.exists (Expr.equal ne) forms);
      make_node [e; ne] (Close e) [] []
  | Enot (Eapp (s, _, _) as e1, _) ->
      assert (List.exists (Expr.equal e1) forms);
      make_node [e1; e] (Close e1) [] []
  | _ -> assert false
;;

let rec decompose_conj n e dirs vars forms taus =
  match e, dirs, vars with
  | Eand (e1, e2, _), L::rest, _ ->
      let n1 = decompose_conj n e1 rest vars forms taus in
      make_node [e] (And (e1, e2)) [[e1]] [n1]
  | Eand (e1, e2, _), R::rest, _ ->
      let n1 = decompose_conj n e2 rest vars forms taus in
      make_node [e] (And (e1, e2)) [[e2]] [n1]
  | Eall (v, ty, e1, _), _, w::rest when n = w ->
      begin match taus with
      | [] -> assert false
      | x::t ->
          let f = Expr.substitute [(v, x)] e1 in
          let n1 = decompose_conj (n+1) f dirs rest forms t in
          make_node [e] (All (e, x)) [[f]] [n1]
      end
  | Eall (v, ty, e1, _), _, _ ->
      let x = emeta (e) in
      let f = Expr.substitute [(v, x)] e1 in
      let n1 = decompose_conj (n+1) f dirs vars forms taus in
      make_node [e] (All (e, x)) [[f]] [n1]
  | Enot (Eor (e1, e2, _), _), L::rest, _ ->
      let ne1 = enot e1 in
      let n1 = decompose_conj n ne1 rest vars forms taus in
      make_node [e] (NotOr (e1, e2)) [[ne1]] [n1]
  | Enot (Eor (e1, e2, _), _), R::rest, _ ->
      let ne2 = enot e2 in
      let n1 = decompose_conj n ne2 rest vars forms taus in
      make_node [e] (NotOr (e1, e2)) [[ne2]] [n1]
  | Enot (Eimply (e1, e2, _), _), L::rest, _ ->
      let n1 = decompose_conj n e1 rest vars forms taus in
      make_node [e] (NotImpl (e1, e2)) [[e1]] [n1]
  | Enot (Eimply (e1, e2, _), _), R::rest, _ ->
      let ne2 = enot e2 in
      let n1 = decompose_conj n ne2 rest vars forms taus in
      make_node [e] (NotOr (e1, e2)) [[ne2]] [n1]
  | Enot (Eex (v, ty, e1, _), _), _, w::rest when n = w ->
      begin match taus with
      | [] -> assert false
      | x::t ->
          let f = Expr.substitute [(v, x)] (enot e1) in
          let n1 = decompose_conj (n+1) f dirs rest forms t in
          make_node [e] (NotEx (e, x)) [[f]] [n1]
      end
  | Enot (Eex (v, ty, e1, _) as e2, _), _, _ ->
      let x = emeta (e2) in
      let f = Expr.substitute [(v, x)] (enot e1) in
      let n1 = decompose_conj (n+1) f dirs vars forms taus in
      make_node [e] (NotEx (e, x)) [[f]] [n1]
  | Enot (Enot (e1, _), _), _, _ ->
      let n1 = decompose_conj n e1 dirs vars forms taus in
      make_node [e] (NotNot e1) [[e1]] [n1]
  | Eequiv (e1, e2, _), L::rest, _ ->
      let ne1 = enot e1 in
      let n1 = decompose_disj ne1 forms in
      let n2 = decompose_disj e2 forms in
      make_node [e] (Equiv (e1, e2)) [[ne1]; [e2]] [n1; n2]
  | Eequiv (e1, e2, _), R::rest, _ ->
      let ne2 = enot e2 in
      let n1 = decompose_disj e1 forms in
      let n2 = decompose_disj ne2 forms in
      make_node [e] (Equiv (e1, e2)) [[ne2]; [e1]] [n2; n1]
  | Enot (Eequiv (e1, e2, _), _), L::rest, _ ->
      let n1 = decompose_disj e1 forms in
      let n2 = decompose_disj e2 forms in
      make_node [e] (NotEquiv (e1, e2)) [[e2]; [e1]] [n2; n1]
  | Enot (Eequiv (e1, e2, _), _), R::rest, _ ->
      let ne1 = enot e1 in
      let ne2 = enot e2 in
      let n1 = decompose_disj ne1 forms in
      let n2 = decompose_disj ne2 forms in
      make_node [e] (NotEquiv (e1, e2)) [[ne1]; [e2]] [n1; n2]
  | _, _, _ ->
      assert (dirs = []);
      assert (vars = []);
      assert (taus = []);
      decompose_disj e forms
;;

let get_proof e =
  let ne = enot e in
  match HE.find hyps_tbl e with
  | Refl ((f, dirs, vars)) ->
      let (f1, tau) = inst_nall ne in
      let n1 = decompose_conj 0 f dirs vars [f1] [tau] in
      let n2 = make_node [ne] (NotAll ne) [[f1]] [n1] in
      (n2, [f])
  | Sym ((f, dirs, vars)) ->
      let (f1, tau1) = inst_nall ne in
      let (f2, tau2) = inst_nall f1 in
      begin match f2 with
      | Enot (Eimply (f3, f4, _), _) ->
          let nf4 = enot f4 in
          let n1 = decompose_conj 0 f dirs vars [f3; nf4] [tau1; tau2] in
          let n2 = make_node [f2] (NotImpl (f3, f4)) [[f3; nf4]] [n1] in
          let n3 = make_node [f1] (NotAll f1) [[f2]] [n2] in
          let n4 = make_node [ne] (NotAll ne) [[f1]] [n3] in
          (n4, [f])
      | _ -> assert false
      end
  | Sym2 (s, (fsy, dirsy, varsy), (ftx, dirtx, vartx)) ->
      let (f1, tau1) = inst_nall ne in
      let (f2, tau2) = inst_nall f1 in
      let rtt = eapp (s, [tau1; tau1]) in
      let nrtt = enot rtt in
      begin match f2 with
      | Enot (Eimply (f3, f4, _), _) ->
          let nf4 = enot f4 in
          let n1 = decompose_conj 0 fsy dirsy varsy [nrtt] [tau1] in
          let n2 = decompose_conj 0 ftx dirtx vartx [rtt; f3; nf4]
                                  [tau1; tau1; tau2]
          in
          let n3 = make_node [] (Cut rtt) [[rtt]; [nrtt]] [n2; n1] in
          let n4 = make_node [f2] (NotImpl (f3, f4)) [[f3; nf4]] [n3] in
          let n5 = make_node [f1] (NotAll f1) [[f2]] [n4] in
          let n6 = make_node [ne] (NotAll ne) [[f1]] [n5] in
          (n6, [fsy; ftx])
      | _ -> assert false
      end
  | Trans ((f, dirs, vars)) ->
      let (f1, tau1) = inst_nall ne in
      let (f2, tau2) = inst_nall f1 in
      let (f3, tau3) = inst_nall f2 in
      begin match f3 with
      | Enot (Eimply (f4, (Eimply (f5, f6, _) as f56), _), _) ->
          let nf6 = enot f6 in
          let n1 = decompose_conj 0 f dirs vars [f4; f5; nf6] [tau1; tau2; tau3]
          in
          let n2 = make_node [f56] (NotImpl (f5, f6)) [[f5; nf6]] [n1] in
          let n3 = make_node [f3] (NotImpl (f4, f56)) [[f4; enot f56]] [n2] in
          let n4 = make_node [f2] (NotAll f2) [[f3]] [n3] in
          let n5 = make_node [f1] (NotAll f1) [[f2]] [n4] in
          let n6 = make_node [ne] (NotAll ne) [[f1]] [n5] in
          (n6, [f])
      | _ -> assert false
      end
  | Trans2 (s, (fsy, dirsy, varsy), (ftx, dirtx, vartx)) ->
      let (f1, tau1) = inst_nall ne in
      let (f2, tau2) = inst_nall f1 in
      let (f3, tau3) = inst_nall f2 in
      let rt1t1 = eapp (s, [tau1; tau1]) in
      let nrt1t1 = enot rt1t1 in
      let rt3t1 = eapp (s, [tau3; tau1]) in
      let nrt3t1 = enot rt3t1 in
      begin match f3 with
      | Enot (Eimply (f4, (Eimply (f5, f6, _) as f56), _), _) ->
          let nf6 = enot f6 in
          let n1 = decompose_conj 0 ftx dirtx vartx [rt3t1; rt1t1; nf6]
                                  [tau3; tau1; tau1]
          in
          let n2 = decompose_conj 0 ftx dirtx vartx [f4; f5; nrt3t1]
                                  [tau1; tau2; tau3]
          in
          let n3 = make_node [] (Cut rt3t1) [[rt3t1]; [nrt3t1]] [n1; n2] in
          let n4 = decompose_conj 0 fsy dirsy varsy [nrt1t1] [tau1] in
          let n5 = make_node [] (Cut rt1t1) [[rt1t1]; [nrt1t1]] [n3; n4] in
          let n6 = make_node [f56] (NotImpl (f5, f6)) [[f5; nf6]] [n5] in
          let n7 = make_node [f3] (NotImpl (f4, f56)) [[f4; enot f56]] [n6] in
          let n8 = make_node [f2] (NotAll f2) [[f3]] [n7] in
          let n9 = make_node [f1] (NotAll f1) [[f2]] [n8] in
          let n10 = make_node [ne] (NotAll ne) [[f1]] [n9] in
          (n10, [fsy; ftx])
      | _ -> assert false
      end
;;

let print_rels oc =
  let f k r =
    Printf.fprintf oc " %s:%s%s%s%s" k
                   (if r.refl = None then "" else "R")
                   (if r.sym = None then "" else "S")
                   (if r.trans = None then "" else "T")
                   (if r.transsym = None then "" else "X")
  in
  Hashtbl.iter f tbl;
;;
