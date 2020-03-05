(*  Copyright 2004 INRIA  *)

open Expr;;

type binop =
  | And
  | Or
  | Imply
  | Equiv
;;

type rule =
  | Rfalse
  | Rnottrue
  | Raxiom of expr
  | Rcut of expr
  | Rnoteq of expr
  | Reqsym of expr * expr
  | Rnotnot of expr
  | Rconnect of binop * expr * expr
  | Rnotconnect of binop * expr * expr
  | Rex of expr * expr
  | Rall of expr * expr
  | Rnotex of expr * expr
  | Rnotall of expr * expr
  | Rpnotp of expr * expr
  | Rnotequal of expr * expr
  | RcongruenceLR of expr * expr * expr
  | RcongruenceRL of expr * expr * expr
  | Rdefinition of string * string * expr list * expr * string option
                   * expr * expr
  | Rextension of string * string * expr list * expr list * expr list list
  | Rlemma of string * expr list
;;

type prooftree = {
  conc : expr list;
  rule : rule;
  hyps : prooftree list;
};;

type lemma = {
  name : string;
  params : (string * Expr.expr) list;
  proof : prooftree;
};;

type proof = lemma list;;

let (@@) = List.rev_append;;

let rec direct_close l =
  match l with
  | [] -> raise Not_found
  | h::t ->
      begin match h with
      | Efalse -> { conc = [h]; rule = Rfalse; hyps = [] }
      | Enot (Etrue, _) -> { conc = [h]; rule = Rnottrue; hyps = [] }
      | Enot (Eapp ("=", [a; b], _), _) when Expr.equal a b ->
        { conc = [h]; rule = Rnoteq (a); hyps = [] }
      | Enot (nh, _) ->
          if List.exists (Expr.equal nh) t then
            { conc = [h; nh]; rule = Raxiom (nh); hyps = [] }
          else
            direct_close t
      | _ ->
          let nh = enot h in
          if List.exists (Expr.equal nh) t then
            { conc = [h; nh]; rule = Raxiom (h); hyps = [] }
          else
            direct_close t
      end
;;

let subsumes super sub =
  List.for_all (fun x -> List.exists (Expr.equal x) super) sub.conc
;;

let lemmas = (Hashtbl.create 997 : (string, lemma) Hashtbl.t);;

let get_lemma name =
  try Hashtbl.find lemmas name
  with Not_found -> assert false
;;

let reduce conc rule hyps =
  let eliminated =
    match rule with
    | Rfalse -> [efalse]
    | Rnottrue -> [enot (etrue)]
    | Raxiom (p) -> [p; enot p]
    | Rcut (p) -> []
    | Rnoteq (a) -> [enot (eapp ("=", [a; a]))]
    | Reqsym (a, b) -> [eapp ("=", [a; b]); enot (eapp ("=", [b; a]))]
    | Rnotnot (p) -> [enot (enot (p))]
    | Rconnect (And, p, q) -> [eand (p, q)]
    | Rconnect (Or, p, q) -> [eor (p, q)]
    | Rconnect (Imply, p, q) -> [eimply (p, q)]
    | Rconnect (Equiv, p, q) -> [eequiv (p, q)]
    | Rnotconnect (And, p, q) -> [enot (eand (p, q))]
    | Rnotconnect (Or, p, q) -> [enot (eor (p, q))]
    | Rnotconnect (Imply, p, q) -> [enot (eimply (p, q))]
    | Rnotconnect (Equiv, p, q) -> [enot (eequiv (p, q))]
    | Rex (ep, v) -> [ep]
    | Rall (ap, t) -> [ap]
    | Rnotex (ep, t) -> [enot (ep)]
    | Rnotall (ap, v) -> [enot (ap)]
    | Rpnotp (p, q) -> [p; q]
    | Rnotequal (a, b) -> [enot (eapp ("=", [a; b]))]
    | RcongruenceLR (p, a, b) -> [apply p a; eapp ("=", [a; b])]
    | RcongruenceRL (p, a, b) -> [apply p a; eapp ("=", [b; a])]
    | Rdefinition (name, sym, args, body, recarg, fld, unf) -> [fld]
    | Rextension (ext, name, args, cons, hyps) -> cons
    | Rlemma (name, args) -> (get_lemma name).proof.conc
  in
  let useful = List.fold_left (fun accu h -> h.conc @@ accu) eliminated hyps in
  List.filter (fun x -> List.exists (Expr.equal x) useful) conc
;;

let rec opt t =
  let nhyps = List.map opt t.hyps in
  try direct_close t.conc
  with Not_found ->
  let nconc = reduce t.conc t.rule nhyps in
  try List.find (subsumes nconc) nhyps
  with Not_found ->
  match t.rule with
  | Rlemma (name, _) ->
     let args = List.map snd (get_lemma name).params in
     { conc = nconc; hyps = nhyps;
       rule = Rlemma (name, args) }
  | _ -> { t with conc = nconc; hyps = nhyps }
;;

let occurs name e = not (Expr.equal e (substitute [(evar name, etrue)] e));;

let optimise p =
  Hashtbl.clear lemmas;
  let f accu lemma =
    let newproof = opt lemma.proof in
    let newlemma = { lemma with proof = newproof } in
    Hashtbl.add lemmas newlemma.name newlemma;
    newlemma :: accu
  in
  List.rev (List.fold_left f [] p)
;;

let rec iter_tree f pt =
  f pt;
  List.iter (iter_tree f) pt.hyps;
;;

let iter f p = List.iter (fun lem -> iter_tree f lem.proof) p;;
