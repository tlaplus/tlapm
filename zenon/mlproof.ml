(*  Copyright 2004 INRIA  *)

open Expr;;
open Printf;;

type rule =
  | Close of expr
  | Close_refl of string * expr
  | Close_sym of string * expr * expr
  | False                       (* false  /             *)
  | NotTrue                     (* -true  /             *)
  | NotNot of expr              (* --p    /  p          *)
  | And of expr * expr          (* p/\q   /  p, q       *)
  | NotOr of expr * expr        (* -(p\/q)  /  -p, -q   *)
  | NotImpl of expr * expr      (* -(p=>q)  /  p, -q    *)
  | NotAll of expr              (* -A.p  /  -p(t(-p))   *)
  | NotAllEx of expr            (* -A.p  /  -p(t(-p)), E.(-p) *)
  | Ex of expr                  (* E.p  /  p(t(p))      *)
  | All of expr * expr          (* A.p  /  p(e)         *)
  | NotEx of expr * expr        (* -E.p  /  -p(e)       *)
  | Or of expr * expr           (* p\/q  /  p | q       *)
  | Impl of expr * expr         (* p=>q  /  -p | q      *)
  | NotAnd of expr * expr       (* -(p/\q)  /  -p | -q  *)
  | Equiv of expr * expr        (* p<=>q  /  -p, -q | p, q *)
  | NotEquiv of expr * expr     (* -(p<=>q)  /  -p, q | p, -q *)
  | P_NotP of expr * expr
  | P_NotP_sym of string * expr * expr
  | NotEqual of expr * expr
  | Definition of definition * expr * expr

  | ConjTree of expr            (* p1/\p2/\...  /  p1, p2, ... *)
  | DisjTree of expr            (* p1\/p2\/...  /  p1 | p2 | ... *)
  | AllPartial of expr * string * int
                                (* Ax.p(x)  /  Axyz.p(s(xyz)) *)
  | NotExPartial of expr * string * int
                                (* -Ex.p(x)  /  -Exyz.p(s(xyz)) *)
  | Refl of string * expr * expr
  | Trans of expr * expr
  | Trans_sym of expr * expr
  | TransEq of expr * expr * expr
  | TransEq2 of expr * expr * expr
  | TransEq_sym of expr * expr * expr

  | Cut of expr
  | CongruenceLR of expr * expr * expr
  | CongruenceRL of expr * expr * expr
  | Miniscope of expr * expr * expr list

  | Ext of string * string * expr list
;;

type proof = {
  mlconc : expr list;      (* conclusion *)
  mlrule : rule;           (* rule *)
  mlhyps : proof array;    (* proof branches *)
  mutable mlrefc : int;    (* reference count *)
};;

let rec size p =
  if p.mlrefc < 0 then 0 else begin
    p.mlrefc <- - p.mlrefc;
    1 + Array.fold_left (fun accu pr -> accu + size pr) 0 p.mlhyps
  end
;;

let rec iter f p =
  f p;
  Array.iter (iter f) p.mlhyps;
;;

let make_node conc rule hyps subs =
  let remove_hyp hyp sub = diff sub.mlconc hyp in
  let extras = List.map2 remove_hyp hyps subs in
  let extra = List.fold_left union [] extras in
  {
    mlconc = union conc extra;
    mlrule = rule;
    mlhyps = Array.of_list subs;
    mlrefc = 1;
  }
;;

let make_cl p =
  make_node [p; enot p] (Close p) [] []
;;

let make_clr r a =
  make_node [enot (eapp (r, [a; a]))] (Close_refl (r, a)) [] []
;;

let make_cls r a b =
  let rab = eapp (r, [a; b]) in
  let nrba = enot (eapp (r, [b; a])) in
  make_node [rab; nrba] (Close_sym (r, a, b)) [] []
;;

let make_f = make_node [efalse] False [] [];;
let make_nt = make_node [enot etrue] NotTrue [] [];;

let make_nn p n0 =
  make_node [enot (enot p)] (NotNot p) [[p]] [n0]
;;

let make_and p q n0 =
  make_node [eand (p, q)] (And (p, q)) [[p; q]] [n0]
;;

let make_nor p q n0 =
  make_node [enot (eor (p, q))] (NotOr (p, q)) [[enot p; enot q]] [n0]
;;

let make_nimpl p q n0 =
  make_node [enot (eimply (p, q))] (NotImpl (p, q)) [[p; enot q]] [n0]
;;

let make_nall nap n0 =
  let (v, t, p) =
    match nap with
    | Enot (Eall (v, t, body, _), _) -> (v, t, body)
    | _ -> assert false
  in
  let tnp = etau (v, t, enot p) in
  let nptnp = enot (substitute [(v, tnp)] p) in
  make_node [nap] (NotAll nap) [[nptnp]] [n0]
;;

let make_ex ep n0 =
  let (v, t, p) =
    match ep with
    | Eex (v, t, body, _) -> (v, t, body)
    | _ -> assert false
  in
  let tp = etau (v, t, p) in
  let ptp = substitute [(v, tp)] p in
  make_node [ep] (Ex ep) [[ptp]] [n0]
;;

let make_all ap a n0 =
  let (v, p) =
    match ap with
    | Eall (v, _, body, _) -> (v, body)
    | _ -> assert false
  in
  let pa = substitute [(v, a)] p in
  make_node [ap] (All (ap, a)) [[pa]] [n0]
;;

let make_nex nep a n0 =
  let (v, p) =
    match nep with
    | Enot (Eall (v, _, body, _), _) -> (v, body)
    | _ -> assert false
  in
  let npa = enot (substitute [(v, a)] p) in
  make_node [nep] (All (nep, a)) [[npa]] [n0]
;;

let make_or p q n0 n1 =
  make_node [eor (p, q)] (Or (p, q)) [[p]; [q]] [n0; n1]
;;

let make_impl p q n0 n1 =
  make_node [eimply (p, q)] (Impl (p, q)) [[enot p]; [q]] [n0; n1]
;;

let make_nand p q n0 n1 =
  make_node [enot (eand (p, q))] (NotAnd (p, q)) [[enot p]; [enot q]] [n0; n1]
;;

let make_eqv p q n0 n1 =
  make_node [eequiv (p, q)] (Equiv (p, q)) [[enot p; enot q]; [p; q]] [n0; n1]
;;

let make_neqv p q n0 n1 =
  make_node [enot (eequiv (p, q))] (NotEquiv (p, q))
            [[enot p; enot q]; [p; q]] [n0; n1]
;;

let mk_neqs l1 l2 =
  try List.map2 (fun x y -> [enot (eapp ("=", [x; y]))]) l1 l2
  with Invalid_argument _ -> assert false
;;

let make_pnp pa npb ns =
  let (p, aa) =
    match pa with
    | Eapp (p, aa, _) -> (p, aa)
    | _ -> assert false
  in
  let bb =
    match npb with
    | Enot (Eapp (q, bb, _), _) -> assert (q = p); bb
    | _ -> assert false
  in
  make_node [pa; npb] (P_NotP (pa, npb)) (mk_neqs aa bb) ns
;;

let make_pnps r rab nrcd n0 n1 =
  let (r, a, b) =
    match rab with
    | Eapp (r, [a; b], _) -> (r, a, b)
    | _ -> assert false
  in
  let (c, d) =
    match nrcd with
    | Enot (Eapp (s, [c; d], _), _) -> assert (s = r); (c, d)
    | _ -> assert false
  in
  make_node [rab; nrcd] (P_NotP_sym (r, rab, nrcd))
            [[enot (eapp ("=", [b; c]))]; [enot (eapp ("=", [a; d]))]] [n0; n1]
;;

let make_neql fa fb ns =
  let (f, aa) =
    match fa with
    | Eapp (f, aa, _) -> (f, aa)
    | _ -> assert false
  in
  let bb =
    match fb with
    | Eapp (g, bb, _) -> assert (g = f); bb
    | _ -> assert false
  in
  make_node [enot (eapp ("=", [fa; fb]))] (NotEqual (fa, fb)) (mk_neqs aa bb) ns
;;

let make_def d folded unfolded n0 =
  make_node [folded] (Definition (d, folded, unfolded)) [[unfolded]] [n0]
;;

let make_conglr p a b n0 =
  make_node [apply p a; eapp ("=", [a; b])] (CongruenceLR (p, a, b))
            [[apply p b]] [n0]
;;

let make_congrl p a b n0 =
  make_node [apply p a; eapp ("=", [b; a])] (CongruenceRL (p, a, b))
            [[apply p b]] [n0]
;;

let make_cut p n0 n1 =
  make_node [] (Cut p) [[p]; [enot p]] [n0; n1]
;;

(*

let make_ctree p ps n0 = assert false;;
let make_dtree p ps ns = assert false;;
let make_allp ap s arity n0 = assert false;;
let make_nexp nep s arity n0 = assert false;;

let make_refl r a b n0 =
  make_node [enot (eapp (r, [a; b]))] (Refl (r, a, b))
            [[enot (eapp ("=", [a; b]))]] [n0]
;;

let make_trans r a b c d n0 n1 =
  let rab = eapp (r, [a; b]) in
  let nrcd = enot (eapp (r, [c; d])) in
  make_node [rab; nrcd] (Trans (rab, nrcd))
            [[enot (eapp ("=", [c; a])); enot (eapp (r, [c; a]))];
             [enot (eapp ("=", [b; d])); enot (eapp (r, [b; d]))]]
            [n0; n1]
;;

let make_transs r a b c d n0 n1 =
  let rab = eapp (r, [a; b]) in
  let nrcd = enot (eapp (r, [c; d])) in
  make_node [rab; nrcd] (Trans_sym (rab, nrcd))
            [[enot (eapp ("=", [d; a])); enot (eapp (r, [d; a]))];
             [enot (eapp ("=", [b; c])); enot (eapp (r, [b; c]))]]
            [n0; n1]
;;

let make_transeq r a b c d n0 n1 =
  let aeb = eapp ("=", [a; b]) in
  let nrcd = enot (eapp (r, [c; d])) in
  let nrca = enot (eapp (r, [c; a])) in
  let nrbd = enot (eapp (r, [b; d])) in
  make_node [aeb; nrcd] (Trans (aeb, nrcd))
            [[enot (eapp ("=", [c; a])); nrca];
             [nrca; nrbd];
             [enot (eapp ("=", [b; d])); nrbd]]
            [n0; n1]
;;

let make_transeqs r a b c d n0 n1 =
  let aeb = eapp ("=", [a; b]) in
  let nrcd = enot (eapp (r, [c; d])) in
  let nrda = enot (eapp (r, [d; a])) in
  let nrbc = enot (eapp (r, [b; c])) in
  make_node [aeb; nrcd] (Trans (aeb, nrcd))
            [[enot (eapp ("=", [d; a])); nrda];
             [nrda; nrbc];
             [enot (eapp ("=", [b; c])); nrbc]]
            [n0; n1]
;;
*)
