(*  Copyright 2008 INRIA  *)

(* Extension for TLA+ : set theory. *)

open Printf;;

open Expr;;
open Misc;;
open Mlproof;;
open Node;;
open Phrase;;

let add_formula e = ();;
let remove_formula e = ();;

let tla_set_constructors = [
  (* "TLA.BOOLEAN"; is an abbrev in Isabelle *)
  "TLA.emptyset";
  "TLA.upair";
  "TLA.addElt";
  "TLA.set";
  "TLA.infinity";
  "TLA.SUBSET";
  "TLA.UNION";
  "TLA.INTER";
  "TLA.cup";
  "TLA.cap";
  "TLA.setminus";
  "TLA.subsetOf";
  "TLA.setOfAll";
  "TLA.FuncSet";
  "TLA.DOMAIN";
  "TLA.Product";
  "arith.N";
  "arith.Z";
  "arith.R";
  "arith.natrange";
  "arith.intrange";
  "TLA.Seq";
  "TLA.recordset";
];;

let tla_fcn_constructors = [
(* Note: $string is not here, even though strings are functions
   Same for TLA.tuple
 *)
  "TLA.Fcn";
  "TLA.except";
  "TLA.oneArg";
  "TLA.extend";
];;

let tla_other_symbols = [
  "TLA.in";
  "TLA.isAFcn";
  "TLA.cond";
  "TLA.CASE";
  "TLA.tuple";
  "TLA.record";
  "TLA.fapply";
  "TLA.box";
];;

let is_set_expr e =
  match e with
  | Evar (v, _) -> List.mem v tla_set_constructors
  | Eapp (f, _, _) -> List.mem f tla_set_constructors
  | _ -> false
;;

let is_fcn_expr e =
  match e with
  | Evar (v, _) -> List.mem v tla_fcn_constructors
  | Eapp (f, _, _) -> List.mem f tla_fcn_constructors
  | _ -> false
;;

let is_notequiv e =
  match e with
  | Eapp ("$notequiv", _, _) -> true
  | _ -> false
;;

let mkbranches hs = Array.of_list (List.map (fun x -> [x]) hs);;

let rec decompose_add e =
  match e with
  | Eapp ("TLA.addElt", [e1; e2], _) ->
     let (l, rest) = decompose_add e2 in (e1 :: l, rest)
  | _ -> ([], e)
;;

let rec get_values_set e =
  match e with
  | Evar ("TLA.emptyset", _) -> ([], false)
  | Eapp ("TLA.upair", [e1; e2], _) -> ([e1; e2], false)
  | Eapp ("TLA.set", l, _) -> (l, false)
  | Eapp ("TLA.addElt", [e1; e2], _) ->
     let (vs, rest) = get_values_set e2 in
     (e1 :: vs, rest)
  | Eapp ("TLA.union", [e1; e2], _) ->
     let (vs1, rest1) = get_values_set e1 in
     let (vs2, rest2) = get_values_set e2 in
     (vs1 @ vs2, rest1 || rest2)
(*| Eapp ("TLA.FuncSet", ...) -> cross-product TODO? *)
  | _ -> ([], true)
;;

let is_var e = match e with Evar _ -> true | _ -> false;;

let rec succ_nat n accu =
  if n <= 0
  then accu
  else succ_nat (n-1) (eapp ("TLA.fapply", [evar "TLA.Succ"; accu]))
;;

let mk_nat n = succ_nat n (evar "0");;

let is_string e = match e with Eapp ("$string", _, _) -> true | _ -> false;;

let trivially_notin e1 e2 =
  match e1, e2 with
  | Eapp ("$string", _, _), Eapp ("TLA.set", elements, _) ->
     let f x = is_string x && not (Expr.equal x e1) in
     List.for_all f elements
  | _ -> false
;;

let rec mk_pairs l =
  match l with
  | [] -> []
  | a :: b :: t -> (a, b) :: (mk_pairs t)
  | _ -> Error.warn "record or record set with odd number of fields"; []
;;

exception Invalid_record

let rec check_record_labels l =
  match l with
  | (Eapp ("$string", [Evar (l1, _)], _), _)
    :: (Eapp ("$string", [Evar (l2, _)], _), _) :: _
    when l1 = l2 ->
     Error.warn (sprintf "duplicate record field %s" l1);
     raise Invalid_record;
  | (l1, _) :: (l2, _) :: t when Expr.equal l1 l2 ->
     Error.warn "duplicate record field (non-string)";
     raise Invalid_record;
  | _ :: t -> check_record_labels t
  | [] -> ()
;;

let get_record_labels l =
  list_sort_unique Expr.compare (List.map fst (mk_pairs l))
;;

let field_trivially_notin rtype (lbl, e) =
  try trivially_notin e (List.assq lbl rtype)
  with Not_found -> true
;;

let newnodes_prop e g =
  let mknode prio name args branches =
    [ Node {
      nconc = [e];
      nrule = Ext ("tla", name, args);
      nprio = prio;
      ngoal = g;
      nbranches = branches;
    } ]
  in
  let mknode_cut prio name args branches =
    [ Node {
      nconc = [];
      nrule = Ext ("tla", name, args);
      nprio = prio;
      ngoal = g;
      nbranches = branches;
    } ]
  in
  let mknode_inst prio m term =
    match m with
    | Eall (v, t, p, _) ->
       let n = Expr.substitute [(v, term)] p in
       [ Node {
         nconc = [m];
         nrule = All (m, term);
         nprio = prio;
         ngoal = g;
         nbranches = [| [n] |];
       } ]
    | Eex (v, t, p, _) ->
       let n = Expr.substitute [(v, term)] (enot p) in
       let nm = enot (m) in
       [ Node {
         nconc = [nm];
         nrule = NotEx (nm, term);
         nprio = prio;
         ngoal = g;
         nbranches = [| [n] |];
       } ]
    | _ -> assert false
  in
  match e with
  | Eapp ("=", [e1; Etrue], _) ->
     mknode Prop "eq_x_true" [e; e1; e1] [| [e1] |]

  | Eapp ("=", [Etrue; e1], _) ->
     mknode Prop "eq_true_x" [e; e1; e1] [| [e1] |]

  | Enot (Eapp ("=", [e1; Etrue], _), _) ->
     let h1 = enot (e1) in
     mknode Prop "noteq_x_true" [e; h1; e1] [| [h1] |]

  | Enot (Eapp ("=", [Etrue; e1], _), _) ->
     let h1 = enot (e1) in
     mknode Prop "noteq_true_x" [e; h1; e1] [| [h1] |]

  | Eapp ("=", [e1; Efalse], _) ->
     let h = enot (e1) in
     mknode Prop "eq_x_false" [e; h; e1] [| [h] |]

  | Eapp ("=", [Efalse; e1], _) ->
     let h = enot (e1) in
     mknode Prop "eq_false_x" [e; h; e1] [| [h] |]

  | Emeta (e1, _) ->
     mknode_inst Arity e1 efalse

  | Enot (Emeta (e1, _), _) ->
     mknode_inst Arity e1 etrue

  | Eapp ("TLA.in", [e1; Evar ("TLA.emptyset", _)], _) ->
    mknode Prop "in_emptyset" [e; e1] [| |]

  | Eapp ("TLA.in", [e1; Eapp ("TLA.upair", [e2; e3], _)], _) ->
    let h1 = eapp ("=", [e1; e2]) in
    let h2 = eapp ("=", [e1; e3]) in
    mknode Prop "in_upair" [e; h1; h2; e1; e2; e3] [| [h1]; [h2] |]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.upair", [e2; e3], _)], _), _) ->
    let h1 = enot (eapp ("=", [e1; e2])) in
    let h2 = enot (eapp ("=", [e1; e3])) in
    mknode Prop "notin_upair" [e; h1; h2; e1; e2; e3] [| [h1; h2] |]

  | Eapp ("TLA.in", [e1; Eapp ("TLA.addElt", [e2; e3], _) as s], _) ->
     let (elems, rest) = decompose_add s in
     let helems = List.map (fun x -> eapp ("=", [e1; x])) elems in
     let hs =
       if Expr.equal rest (evar "TLA.emptyset") then helems
       else helems @ [eapp ("TLA.in", [e1; rest])]
     in
     mknode Prop "in_addElt" [e; e1; s] (mkbranches hs)
  | Eapp ("TLA.in", [e1; Eapp ("TLA.set", elems, _) as s], _) ->
     let helems = List.map (fun x -> eapp ("=", [e1; x])) elems in
     mknode Prop "in_set" [e; e1; s] (mkbranches helems)
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.addElt", [e2; e3], _) as s], _), _) ->
     let (elems, rest) = decompose_add s in
     let helems = List.map (fun x -> enot (eapp ("=", [e1; x]))) elems in
     let hs =
       if Expr.equal rest (evar "TLA.emptyset") then helems
       else enot (eapp ("TLA.in", [e1; rest])) :: helems
     in
     mknode Prop "notin_addElt" [e; e1; s] [| hs |]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.set", elems, _) as s], _), _) ->
     let helems = List.map (fun x -> enot (eapp ("=", [e1; x]))) elems in
     mknode Prop "notin_set" [e; e1; s] [| helems |]

  | Enot (Eapp ("TLA.in", [e1; Emeta (m, _)], _), _) ->
     mknode_inst (Inst m) m (eapp ("TLA.set", [e1]))

  (* infinity -- needed ? *)

  | Eapp ("TLA.in", [e1; Eapp ("TLA.SUBSET", [s], _)], _) ->
     let h1 = eapp ("TLA.subseteq", [e1; s]) in
     mknode Prop "in_SUBSET" [e; h1; e1; s] [| [h1] |]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.SUBSET", [s], _)], _), _) ->
     let h1 = enot (eapp ("TLA.subseteq", [e1; s])) in
     mknode Prop "notin_SUBSET" [e; h1; e1; s] [| [h1] |]

  | Eapp ("TLA.in", [e1; Eapp ("TLA.UNION", [s], _)], _) ->
     let b = Expr.newvar () in
     let h1 = eex (b, "", eand (eapp ("TLA.in", [b; s]),
                                eapp ("TLA.in", [e1; b]))) in
     mknode Prop "in_UNION" [e; h1; e1; s] [| [h1] |]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.UNION", [s], _)], _), _) ->
     let b = Expr.newvar () in
     let h1 = enot (eex (b, "", eand (eapp ("TLA.in", [b; s]),
                                      eapp ("TLA.in", [e1; b])))) in
     mknode Arity "notin_UNION" [e; h1; e1; s] [| [h1] |]

  (* INTER -- needed ? *)

  | Eapp ("TLA.in", [e1; Eapp ("TLA.cup", [e2; e3], _)], _) ->
     let h1 = eapp ("TLA.in", [e1; e2]) in
     let h2 = eapp ("TLA.in", [e1; e3]) in
     mknode Prop "in_cup" [e; h1; h2; e1; e2; e3] [| [h1]; [h2] |]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.cup", [e2; e3], _)], _), _) ->
     let h1 = enot (eapp ("TLA.in", [e1; e2])) in
     let h2 = enot (eapp ("TLA.in", [e1; e3])) in
     mknode Prop "notin_cup" [e; h1; h2; e1; e2; e3] [| [h1; h2] |]

  | Eapp ("TLA.in", [e1; Eapp ("TLA.cap", [e2; e3], _)], _) ->
     let h1 = eapp ("TLA.in", [e1; e2]) in
     let h2 = eapp ("TLA.in", [e1; e3]) in
     mknode Prop "in_cap" [e; h1; h2; e1; e2; e3] [| [h1; h2] |]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.cap", [e2; e3], _)], _), _) ->
     let h1 = enot (eapp ("TLA.in", [e1; e2])) in
     let h2 = enot (eapp ("TLA.in", [e1; e3])) in
     mknode Prop "notin_cap" [e; h1; h2; e1; e2; e3] [| [h1]; [h2] |]

  | Eapp ("TLA.in", [e1; Eapp ("TLA.setminus", [e2; e3], _)], _) ->
     let h1 = eapp ("TLA.in", [e1; e2]) in
     let h2 = enot (eapp ("TLA.in", [e1; e3])) in
     mknode Prop "in_setminus" [e; h1; h2; e1; e2; e3] [| [h1; h2] |]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.setminus", [e2; e3], _)], _), _) ->
     let h1 = enot (eapp ("TLA.in", [e1; e2])) in
     let h2 = eapp ("TLA.in", [e1; e3]) in
     mknode Prop "notin_setminus" [e; h1; h2; e1; e2; e3] [| [h1]; [h2] |]

  | Eapp ("TLA.in",
          [e1; Eapp ("TLA.subsetOf", [s; Elam (v, _, p, _) as pred], _)],
          _) ->
     let h1 = eapp ("TLA.in", [e1; s]) in
     let h2 = substitute [(v, e1)] p in
     mknode Prop "in_subsetof" [e; h1; h2; e1; s; pred] [| [h1; h2] |]
  | Enot (Eapp ("TLA.in",
                [e1; Eapp ("TLA.subsetOf", [s; Elam (v, _, p, _) as pred], _)],
                _), _) ->
     let h1 = enot (eapp ("TLA.in", [e1; s])) in
     let h2 = enot (substitute [(v, e1)] p) in
     mknode Prop "notin_subsetof" [e; h1; h2; e1; s; pred] [| [h1]; [h2] |]

  | Eapp ("TLA.in",
          [e1; Eapp ("TLA.setOfAll", [s; Elam (v, _, p, _) as pred], _)],
          _) ->
     let x = Expr.newvar () in
     let h1 = eex (x, "", eand (eapp ("TLA.in", [x; s]),
                                eapp ("=", [e1; substitute [(v, x)] p])))
     in
     mknode (Inst h1) "in_setofall" [e; h1; e1; s; pred] [| [h1] |]
  | Enot (Eapp ("TLA.in",
                [e1; Eapp ("TLA.setOfAll", [s; Elam (v, _, p, _) as pred], _)],
                _), _) ->
     let x = Expr.newvar () in
     let h1 = enot (eex (x, "", eand (eapp ("TLA.in", [x; s]),
                                      eapp ("=", [e1; substitute [(v, x)] p]))))
     in
     mknode (Inst h1) "notin_setofall" [e; h1; e1; s; pred] [| [h1] |]

  | Eapp ("TLA.in", [f; Eapp ("TLA.FuncSet", [a; b], _)], _) ->
     let h1 = eapp ("TLA.isAFcn", [f]) in
     let h2 = eapp ("=", [eapp ("TLA.DOMAIN", [f]); a]) in
     let x = Expr.newvar () in
     let h3 = eall (x, "",
                eimply (eapp ("TLA.in", [x; a]),
                        eapp ("TLA.in", [eapp ("TLA.fapply", [f; x]); b])))
     in
     mknode Arity "in_funcset" [e; h1; h2; h3; f; a; b] [| [h1; h2] |] @
     mknode (Inst h3) "in_funcset" [e; h1; h2; h3; f; a; b] [| [h1; h2; h3] |]

  | Enot (Eapp ("TLA.in", [f; Eapp ("TLA.FuncSet", [a; b], _)], _), _) ->
     let h1 = enot (eapp ("TLA.isAFcn", [f])) in
     let h2 = enot (eapp ("=", [eapp ("TLA.DOMAIN", [f]); a])) in
     let x = Expr.newvar () in
     let h3 = enot (
               eall (x, "",
                     eimply (eapp ("TLA.in", [x; a]),
                             eapp ("TLA.in", [eapp ("TLA.fapply", [f; x]); b]))))
     in
     let prio =
       match f with
       | Eapp (s, _, _) when List.mem s tla_fcn_constructors -> Arity
       | _ -> Inst h3
     in
     let shortcut =
       match f with
       | Eapp ("TLA.except", [f1; v; e1], _) ->
          let h1 = enot (eapp ("TLA.in", [f1; eapp ("TLA.FuncSet", [a; b])])) in
          let h2 = enot (eapp ("TLA.in", [e1; b])) in
          mknode Arity "except_notin_funcset" [e; h1; h2; f1; v; e1; a; b]
                 [| [h1]; [h2] |]
       | _ -> []
     in
     shortcut @ mknode prio "notin_funcset" [e; h1; h2; h3; f; a; b]
            [| [h1]; [h2]; [h3] |]

  | Eapp ("=", [e1; Evar ("TLA.emptyset", _)], _) ->
     let x = Expr.newvar () in
     let h = eall (x, "", enot (eapp ("TLA.in", [x; e1]))) in
     mknode Arity "setequalempty" [e; h; e1] [| [h] |]

  | Eapp ("=", [Evar ("TLA.emptyset", _); e1], _) ->
     let x = Expr.newvar () in
     let h = eall (x, "", enot (eapp ("TLA.in", [x; e1]))) in
     mknode Arity "setemptyequal" [e; h; e1] [| [h] |]

(* redundant ?
  | Eapp ("=", [e1; e2], _) when is_set_expr e1 || is_set_expr e2 ->
     let x = Expr.newvar () in
     let h = eall (x, "", eequiv (eapp ("TLA.in", [x; e1]),
                                  eapp ("TLA.in", [x; e2])))
     in
     mknode (Inst h) "setequal" [e; h; e1; e2] [| [h] |]
*)

  | Eapp ("=", [e1; e2], _) when is_set_expr e1 || is_set_expr e2 ->
     let x = Expr.newvar () in
     let h = eall (x, "", eequiv (eapp ("TLA.in", [x; e1]),
                                  eapp ("TLA.in", [x; e2])))
     in
     mknode (Inst h) "setequal" [e; h; e1; e2] [| [h] |]
  | Enot (Eapp ("=", [e1; e2], _), _) when is_set_expr e1 || is_set_expr e2 ->
     let x = Expr.newvar () in
     let h = enot (eall (x, "", eequiv (eapp ("TLA.in", [x; e1]),
                                        eapp ("TLA.in", [x; e2]))))
     in
     mknode (Inst h) "notsetequal" [e; h; e1; e2] [| [h] |]

  | Enot (Eapp ("TLA.isAFcn", [Eapp ("TLA.Fcn", [s; l], _)], _), _) ->
     mknode Prop "notisafcn_fcn" [e; s; l] [| |]

  | Enot (Eapp ("TLA.isAFcn", [Eapp ("TLA.except", [f; v; e1], _)], _), _) ->
     mknode Prop "notisafcn_except" [e; f; v; e1] [| |]

  | Enot (Eapp ("TLA.isAFcn", [Eapp ("TLA.oneArg", [e1; e2], _)], _), _) ->
     mknode Prop "notisafcn_onearg" [e; e1; e2] [| |]

  | Enot (Eapp ("TLA.isAFcn", [Eapp ("TLA.extend", [f; g], _)], _), _) ->
     mknode Prop "notisafcn_extend" [e; f; g] [| |]

  | Eapp ("=", [e1; e2], _)
    when (is_fcn_expr e1 || is_fcn_expr e2)
        (* && not (is_var e1) && not (is_var e2) *) ->
     let x = Expr.newvar () in
     let h1 = eequiv (eapp ("TLA.isAFcn", [e1]), eapp ("TLA.isAFcn", [e2])) in
     let h2 = eapp ("=", [eapp ("TLA.DOMAIN", [e1]); eapp ("TLA.DOMAIN", [e2])])
     in
     let h3 = eall (x, "", eapp ("=", [eapp ("TLA.fapply", [e1; x]);
                                       eapp ("TLA.fapply", [e2; x])]))
     in
     let h = eand (eand (h1, h2), h3) in
     mknode (Inst h3) "funequal" [e; h; e1; e2] [| [h] |]
  | Enot (Eapp ("=", [e1; e2], _), _) when is_fcn_expr e1 || is_fcn_expr e2 ->
     let x = Expr.newvar () in
     let h0 = eapp ("TLA.isAFcn", [e1]) in
     let h1 = eapp ("TLA.isAFcn", [e2]) in
     let h2 = eapp ("=", [eapp ("TLA.DOMAIN", [e1]); eapp ("TLA.DOMAIN", [e2])])
     in
     let h3 = eall (x, "", eimply (eapp ("TLA.in", [x; eapp("TLA.DOMAIN",[e2])]),
                                   eapp ("=", [eapp ("TLA.fapply", [e1; x]);
                                               eapp ("TLA.fapply", [e2; x])])))
     in
     let h = enot (eand (eand (eand (h0, h1), h2), h3)) in
     mknode (Inst h3) "notfunequal" [e; h; e1; e2] [| [h] |]

  | Enot (Eapp ("=", [Etau (v1, t1, p1, _); Etau (v2, t2, p2, _)], _), _)
    when not (is_notequiv p1) && not (is_notequiv p2) ->
     let x = Expr.newvar () in
     let p1x = substitute [(v1, x)] p1 in
     let p2x = substitute [(v2, x)] p2 in
     let h = eex (x, t1, eapp ("$notequiv", [p1x; p2x])) in
     mknode (Inst h) "choose_diff_choose"
            [e; h; elam (v1, t1, p1); elam (v2, t2, p2)] [| [h] |]

  | Eapp ("$notequiv", [e1; e2], _) ->
     let h = enot (eequiv (e1, e2)) in
     mknode Arity "notequivdef" [] [| [h] |]

  | Enot (Eapp ("=", [e1; Etau (v2, t2, p2, _)], _), _)
  | Enot (Eapp ("=", [Etau (v2, t2, p2, _); e1], _), _)
  ->
     let h1 = eex (v2, t2, p2) in
     let h2a = enot (eex (v2, t2, p2)) in
     let h2b = enot (substitute [(v2, e1)] p2) in
     mknode_cut (Inst h2a) "notequalchoose"
                [h1; h2a; h2b; elam (v2, t2, p2); e1]
                [| [h1]; [h2a; h2b] |]

  | Eall (v, t, Eimply (Eapp ("TLA.in",
                              [vv; ( Eapp (("TLA.addElt" | "TLA.upair"
                                            | "TLA.set" | "TLA.union"), _, _)
                                   | Evar ("TLA.emptyset", _)
                                   ) as s], _), _, _), _) ->
     let (elems, rest) = get_values_set s in
     let nodes = List.map (fun elem -> mknode_inst Arity e elem) elems in
     List.flatten nodes @ (if rest then [] else [Stop])
  | Enot ((Eex (v, t, Eand (Eapp ("TLA.in",
                                  [vv; ( Eapp (("TLA.addElt" | "TLA.upair"
                                                | "TLA.set" | "TLA.union"), _, _)
                                       | Evar ("TLA.emptyset", _)
                                       ) as s], _), _, _), _) as ex), _) ->
     let (elems, rest) = get_values_set s in
     let nodes = List.map (fun elem -> mknode_inst Arity ex elem) elems in
     List.flatten nodes @ (if rest then [] else [Stop])

  | Enot (Eapp ("TLA.in", [Evar ("0", _); Evar ("arith.N", _)], _), _) ->
     mknode Prop "in_nat_0" [e] [| |]
  | Enot (Eapp ("TLA.in", [Eapp ("TLA.fapply", [Evar ("TLA.Succ", _); e1], _);
                           Evar ("arith.N", _)], _), _) ->
     let h = enot (eapp ("TLA.in", [e1; evar "arith.N"])) in
     mknode Prop "in_nat_succ" [e; h; e1] [| [h] |]
  | Enot (Eapp ("TLA.in", [Emeta (m, _); Evar ("arith.N", _)], _), _) ->
     mknode_inst (Inst m) m (evar "0")

  | Eapp ("TLA.in", [Emeta _; s], _)
  | Enot (Eapp ("TLA.in", [Emeta _; s], _), _) ->
     let x = Expr.newvar () in
     let f eneq =
       match eneq with
       | Enot (Eapp ("=", [s1; s2], _), _) ->
          let h = enot (eall (x, "", eequiv (eapp ("TLA.in", [x; s1]),
                                             eapp ("TLA.in", [x; s2]))))
          in
          mknode (Inst h) "notsetequal" [eneq; h; s1; s2] [| [h] |]
       | _ -> assert false
     in List.flatten (List.map f (Index.find_neq s))

  | Eapp ("TLA.box", [e1], _) ->
     mknode Prop "box_p" [e; e1] [| [e1] |]

(* tuples *)

  | Eapp ("=", [Eapp ("TLA.tuple", args1, _); Eapp ("TLA.tuple", args2, _)], _)
    when List.length args1 = List.length args2 ->
     let hs = List.map2 (fun a1 a2 -> eapp ("=", [a1; a2])) args1 args2 in
     mknode Prop "tuple_eq_match" (e :: hs) [| hs |]
  | Eapp ("=", [Eapp ("TLA.tuple", args1,_); Eapp ("TLA.tuple", args2,_)],_) ->
     mknode Prop "tuple_eq_mismatch" [e; e] [| |]
  | Eapp ("TLA.in", [e1; Eapp ("TLA.Product",
                               [Eapp ("TLA.tuple", args, _) as e2], _)], _) ->
     let mk_h arg i =
       eapp ("TLA.in", [eapp ("TLA.fapply", [e1; mk_nat i]); arg])
     in
     let hs = list_mapi mk_h args 1 in
     let n = mk_nat (List.length args) in
     let h0 = eapp ("TLA.isASeq", [e1]) in
     let h1 = eapp ("=", [eapp ("TLA.Len", [e1]); n]) in
     mknode Prop "in_product" (e :: e1 :: e2 :: h0 :: h1 :: hs)
            [| h0 :: h1 :: hs |]
  | Enot (Eapp ("TLA.in", [Eapp ("TLA.tuple", a1, _);
                           Eapp ("TLA.Product",
                                     [Eapp ("TLA.tuple", a2, _)], _)],_),_)
    when List.length a1 <> List.length a2
         || List.exists2 trivially_notin a1 a2 ->
     []
  | Enot (Eapp ("TLA.in",
                [e1; Eapp ("TLA.Product",
                           [Eapp ("TLA.tuple", args, _) as e2], _)],_),_) ->
     let mk_h arg i =
       enot (eapp ("TLA.in", [eapp ("TLA.fapply", [e1; mk_nat i]); arg]))
     in
     let hs = list_mapi mk_h args 1 in
     let n = mk_nat (List.length args) in
     let h0 = enot (eapp ("TLA.isASeq", [e1])) in
     let h1 = enot (eapp ("=", [eapp ("TLA.Len", [e1]); n])) in
     let hh = h0 :: h1 :: hs in
     let branches = List.map (fun x -> [x]) hh in
     mknode Prop "notin_product" (e :: e1 :: e2 :: hh) (Array.of_list branches)
  | Enot (Eapp ("TLA.isASeq", [Eapp ("TLA.tuple", _, _)], _), _) ->
     mknode Prop "tuple_notisaseq" [e] [| |]

(* records *)

  | Eapp ("=", [Eapp ("TLA.record", args1, _); Eapp ("TLA.record", args2, _)], _)
  -> begin try
       let cmp (a1, a2) (b1, b2) = Expr.compare a1 b1 in
       let args1 = List.sort cmp (mk_pairs args1) in
       let args2 = List.sort cmp (mk_pairs args2) in
       check_record_labels args1;
       check_record_labels args2;
       let rec mk_hyps as1 as2 =
         match as1, as2 with
         | [], [] -> []
         | (l1, a1) :: t1, (l2, a2) :: t2 when Expr.equal l1 l2 ->
            eapp ("=", [a1; a2]) :: mk_hyps t1 t2
         | _ -> raise Exit
       in
       let hs = mk_hyps args1 args2 in
       mknode Prop "record_eq_match" (e :: hs) [| hs |]
     with
     | Invalid_record -> []
     | Exit -> mknode Prop "record_eq_mismatch" [e; e] [| |]
     end
  | Enot (Eapp ("=", [Eapp ("TLA.record", args1, _);
                      Eapp ("TLA.record", args2, _)], _), _) ->
     begin try
       let cmp (a1, a2) (b1, b2) = Expr.compare a1 b1 in
       let args1 = List.sort cmp (mk_pairs args1) in
       let args2 = List.sort cmp (mk_pairs args2) in
       check_record_labels args1;
       check_record_labels args2;
       let rec mk_hyps as1 as2 =
         match as1, as2 with
         | [], [] -> []
         | (l1, a1) :: t1, (l2, a2) :: t2 when Expr.equal l1 l2 ->
            enot (eapp ("=", [a1; a2])) :: mk_hyps t1 t2
         | _ -> raise Exit
       in
       let hs = mk_hyps args1 args2 in
       let branches = Array.of_list (List.map (fun x -> [x]) hs) in
       mknode Prop "record_neq_match" (e :: hs) branches
     with
     | Invalid_record -> []
     | Exit -> []
     end
  | Enot (Eapp ("=", [e1; Eapp ("TLA.record", args, _) as e2], _), _) ->
     let l_args = mk_pairs args in
     let mk_h (l, arg) =
       enot (eapp ("=", [eapp ("TLA.fapply", [e1; l]); arg]))
     in
     let hs = List.map mk_h l_args in
     let lbls = eapp ("TLA.set", List.map fst l_args) in
     let h0 = enot (eapp ("TLA.isAFcn", [e1])) in
     let h1 = enot (eapp ("=", [eapp ("TLA.DOMAIN", [e1]); lbls])) in
     let hh = h0 :: h1 :: hs in
     let branches = Array.of_list (List.map (fun x -> [x]) hh) in
     mknode Prop "neq_record" (e :: e1 :: e2 :: hh) branches
  | Enot (Eapp ("=", [Eapp ("TLA.record", args, _) as e2; e1], _), _) ->
     let l_args = mk_pairs args in
     let mk_h (l, arg) =
       enot (eapp ("=", [eapp ("TLA.fapply", [e1; l]); arg]))
     in
     let hs = List.map mk_h l_args in
     let lbls = eapp ("TLA.set", List.map fst l_args) in
     let h0 = enot (eapp ("TLA.isAFcn", [e1])) in
     let h1 = enot (eapp ("=", [eapp ("TLA.DOMAIN", [e1]); lbls])) in
     let hh = h0 :: h1 :: hs in
     let branches = Array.of_list (List.map (fun x -> [x]) hh) in
     mknode Prop "record_neq" (e :: e1 :: e2 :: hh) branches
  | Eapp ("TLA.in", [e1; (Eapp ("TLA.recordset", args, _) as e2)], _) ->
     let l_args = mk_pairs args in
     let mk_h (l, arg) = eapp ("TLA.in", [eapp ("TLA.fapply", [e1; l]); arg]) in
     let hs = List.map mk_h l_args in
     let lbls = eapp ("TLA.set", List.map fst l_args) in
     let h0 = eapp ("TLA.isAFcn", [e1]) in
     let h1 = eapp ("=", [eapp ("TLA.DOMAIN", [e1]); lbls]) in
     mknode Prop "in_recordset" (e :: e1 :: e2 :: h0 :: h1 :: hs)
            [| h0 :: h1 :: hs |]
  | Enot (Eapp ("TLA.in", [Eapp ("TLA.record", a1, _);
                           Eapp ("TLA.recordset", a2, _)], _), _)
    when get_record_labels a1 <> get_record_labels a2
         || List.exists (field_trivially_notin (mk_pairs a2)) (mk_pairs a1) ->
     []
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.recordset", args, _) as e2], _), _) ->
     let l_args = mk_pairs args in
     let mk_h (l, arg) =
       enot (eapp ("TLA.in", [eapp ("TLA.fapply", [e1; l]); arg]))
     in
     let hs = List.map mk_h l_args in
     let lbls = eapp ("TLA.set", List.map fst (mk_pairs args)) in
     let h0 = enot (eapp ("TLA.isAFcn", [e1])) in
     let h1 = enot (eapp ("=", [eapp ("TLA.DOMAIN", [e1]); lbls])) in
     let hh = h0 :: h1 :: hs in
     let branches = List.map (fun x -> [x]) hh in
     mknode Prop "notin_recordset" (e :: e1 :: e2 :: hh)
            (Array.of_list branches)
  | Enot (Eapp ("TLA.isAFcn", [Eapp ("TLA.record", _, _)], _), _) ->
     mknode Prop "record_notisafcn" [e] [| |]

(* shortcuts for subseteq *)

  | Eapp ("TLA.subseteq", [Eapp ("TLA.cup", [e1; e2], _); e3], _) ->
     let h1 = eapp ("TLA.subseteq", [e1; e3]) in
     let h2 = eapp ("TLA.subseteq", [e2; e3]) in
     mknode Arity "cup_subseteq" [e; h1; h2] [| [h1; h2] |]
  | Enot (Eapp ("TLA.subseteq", [Eapp ("TLA.cup", [e1; e2], _); e3], _), _) ->
     let h1 = enot (eapp ("TLA.subseteq", [e1; e3])) in
     let h2 = enot (eapp ("TLA.subseteq", [e2; e3])) in
     mknode Arity "not_cup_subseteq" [e; h1; h2] [| [h1]; [h2] |]
  | Eapp ("TLA.subseteq", [e1; Eapp ("TLA.cap", [e2; e3], _)], _) ->
     let h1 = eapp ("TLA.subseteq", [e1; e3]) in
     let h2 = eapp ("TLA.subseteq", [e1; e3]) in
     mknode Arity "subseteq_cap" [e; h1; h2] [| [h1; h2] |]
  | Enot (Eapp ("TLA.subseteq", [e1; Eapp ("TLA.cap", [e2; e3], _)], _), _) ->
     let h1 = enot (eapp ("TLA.subseteq", [e1; e3])) in
     let h2 = enot (eapp ("TLA.subseteq", [e1; e3])) in
     mknode Arity "not_subseteq_cap" [e; h1; h2] [| [h1]; [h2] |]

  | _ -> []
;;

let newnodes_inst_bounded e g =
  let prio = Inst e in  (* FIXME change to Arity ? *)
  match e with
  | Eapp ("TLA.in", [a; s], _) when not (has_metas a) ->
     let get_p (e1, _) =
       match e1 with
       | Eapp ("TLA.bAll", [s1; p], _) when Expr.equal s1 s -> [(e1, p)]
       | Enot (Eapp ("TLA.bEx", [s1; p], _), _) when Expr.equal s1 s ->
         [(e1, p)]
       | _ -> []
     in
     let univ = List.flatten (List.map get_p (Index.find_pos "TLA.bAll")) in
     let exist = List.flatten (List.map get_p (Index.find_neg "TLA.bEx")) in
     let mk_inst_all (f, p) =
       let h = apply p a in
       Node {
         nconc = [e; f];
         nrule = Ext ("tla", "all_in", [f; e; h; s; p]);
         nprio = prio;
         ngoal = g;
         nbranches = [| [h] |];
       }
     in
     let mk_inst_notex (f, p) =
       let h = enot (apply p a) in
       Node {
         nconc = [e; f];
         nrule = Ext ("tla", "notex_in", [f; e; h; s; p]);
         nprio = prio;
         ngoal = g;
         nbranches = [| [h] |];
       }
     in
     List.map mk_inst_all univ @@ List.map mk_inst_notex exist
  | Eapp ("TLA.bAll", [s; p], _) ->
     let get_value (f, _) =
       match f with
       | Eapp ("TLA.in", [a; s1], _) when not (has_metas a) && Expr.equal s s1 ->
          [(f, a)]
       | _ -> []
     in
     let values = List.flatten (List.map get_value (Index.find_pos "TLA.in")) in
     let mk_inst (f, v) =
       let h = apply p v in
       Node {
         nconc = [f; e];
         nrule = Ext ("tla", "all_in", [e; f; h; s; p]);
         nprio = prio;
         ngoal = g;
         nbranches = [| [h] |];
       }
     in
     List.map mk_inst values
  | Enot (Eapp ("TLA.bEx", [s; p], _), _) ->
     let get_value (f, _) =
       match f with
       | Eapp ("TLA.in", [a; s1], _) when not (has_metas a) && Expr.equal s s1 ->
          [(f, a)]
       | _ -> []
     in
     let values = List.flatten (List.map get_value (Index.find_pos "TLA.in")) in
     let mk_inst (f, v) =
       let h = enot (apply p v) in
       Node {
         nconc = [f; e];
         nrule = Ext ("tla", "notex_in", [e; f; h; s; p]);
         nprio = prio;
         ngoal = g;
         nbranches = [| [h] |];
       }
     in
     List.map mk_inst values
  | _ -> []
;;

let strip_neg e = match e with Enot (ne, _) -> ne | _ -> assert false;;

let mknode_pos_l (e, e1, e2, g) =
  let eq = eapp ("=", [e1; e2]) in
  let h1 = enot (eapp ("=", [e; e1])) in
  Node {
    nconc = [e; eq];
    nrule = Ext ("tla", "p_eq_l", [e; eq; h1; e2; e; e1; e2]);
    nprio = Arity_eq;
    ngoal = g;
    nbranches = [| [h1]; [e2] |];
  }
;;

let mknode_pos_r (e, e1, e2, g) =
  let eq = eapp ("=", [e1; e2]) in
  let h1 = enot (eapp ("=", [e; e2])) in
  Node {
    nconc = [e; eq];
    nrule = Ext ("tla", "p_eq_r", [e; eq; h1; e1; e; e1; e2]);
    nprio = Arity_eq;
    ngoal = g;
    nbranches = [| [h1]; [e1] |];
  }
;;

let mknode_neg_l (e, e1, e2, g) =
  let ne = strip_neg e in
  let eq = eapp ("=", [e1; e2]) in
  let h1 = enot (eapp ("=", [ne; e1])) in
  let h2 = enot (e2) in
  Node {
    nconc = [e; eq];
    nrule = Ext ("tla", "np_eq_l", [e; eq; h1; h2; ne; e1; e2]);
    nprio = Arity_eq;
    ngoal = g;
    nbranches = [| [h1]; [h2] |];
  }
;;

let mknode_neg_r (e, e1, e2, g) =
  let ne = strip_neg e in
  let eq = eapp ("=", [e1; e2]) in
  let h1 = enot (eapp ("=", [ne; e2])) in
  let h2 = enot (e1) in
  Node {
    nconc = [e; eq];
    nrule = Ext ("tla", "np_eq_r", [e; eq; h1; h2; ne; e1; e2]);
    nprio = Arity_eq;
    ngoal = g;
    nbranches = [| [h1]; [h2] |];
  }
;;

let newnodes_prop_eq e g =
  let decompose eq =
    match eq with
    | Eapp ("=", [e1; e2], _) -> (e, e1, e2, g)
    | Enot (Eapp ("=", [e1; e2], _), _) -> (e, e1, e2, g)
    | _ -> assert false
  in
  match e with
  | Eapp (s, args, _) ->
     let matches_l = Index.find_trans_left "=" (Index.Sym s) in
     let matches_r = Index.find_trans_right "=" (Index.Sym s) in
     List.map (fun (eq, _) -> mknode_pos_l (decompose eq)) matches_l
     @ List.map (fun (eq, _) -> mknode_pos_r (decompose eq)) matches_r
  | Enot (Eapp (s, args, _), _) ->
     let matches_l = Index.find_trans_left "=" (Index.Sym s) in
     let matches_r = Index.find_trans_right "=" (Index.Sym s) in
     List.map (fun (eq, _) -> mknode_neg_l (decompose eq)) matches_l
     @ List.map (fun (eq, _) -> mknode_neg_r (decompose eq)) matches_r
  | _ -> []
;;

let newnodes_eq_prop_l e g =
  match e with
  | Eapp ("=", [Eapp (s, _, _) as e1; e2], _) ->
     let matches_p = Index.find_pos s in
     let matches_n = Index.find_neg s in
     List.map (fun (e, gg) -> mknode_pos_l (e, e1, e2, gg)) matches_p
     @ List.map (fun (e, gg) -> mknode_neg_l (e, e1, e2, gg)) matches_n
  | _ -> []
;;

let newnodes_eq_prop_r e g =
  match e with
  | Eapp ("=", [e1; Eapp (s, _, _) as e2], _) ->
     let matches_p = Index.find_pos s in
     let matches_n = Index.find_neg s in
     List.map (fun (e, gg) -> mknode_pos_r (e, e1, e2, gg)) matches_p
     @ List.map (fun (e, gg) -> mknode_neg_r (e, e1, e2, gg)) matches_n
  | _ -> []
;;

let has_subst e = Index.find_eq_lr e <> [] || Index.find_eq_rl e <> [];;

let do_substitutions v p g =
  let rhs = Index.find_eq_lr v in
  let lhs = Index.find_eq_rl v in
  let f lr e =
    let eqn = eapp ("=", if lr then [v; e] else [e; v]) in
    Node {
      nconc = [apply p v; eqn];
      nrule = if lr then CongruenceLR (p, v, e) else CongruenceRL (p, v, e);
      nprio = Arity;
      ngoal = g;
      nbranches = [| [apply p e] |];
    }
  in
  List.map (f true) rhs @@ List.map (f false) lhs
;;

let rec newnodes_subst x ctx e g =
  let appctx e = substitute [(x, e)] ctx in
  match e with
  | Evar _ -> []
  | Emeta _ -> []
  | Enot (e1, _) -> newnodes_subst x (appctx (enot x)) e1 g

  | Eapp ("TLA.in", [Evar _ as e1; e2], _) when has_subst e1 ->
     let nctx = appctx (eapp ("TLA.in", [x; e2])) in
     do_substitutions e1 (elam (x, "", nctx)) g
  | Eapp ("TLA.in", [e1; Evar _ as e2], _) when has_subst e2 ->
     let nctx = appctx (eapp ("TLA.in", [e1; x])) in
     do_substitutions e2 (elam (x, "", nctx)) g
(* TODO:
  | Eapp ("TLA.fapply", [Eapp ("$string", [Evar (s, _)], _);
                         <some nat constant in range>], _) ->
     get the nth char and convert it to Isabelle notation
*)

  | Eapp ("TLA.fapply", [Evar _ as e1; e2], _) when has_subst e1 ->
     let nctx = appctx (eapp ("TLA.fapply", [x; e2])) in
     do_substitutions e1 (elam (x, "", nctx)) g
  | Eapp ("TLA.isAFcn", [Evar _ as e1], _) when has_subst e1 ->
     let nctx = appctx (eapp ("TLA.isAFcn", [x])) in
     do_substitutions e1 (elam (x, "", nctx)) g

  | Eapp ("TLA.isASeq", [Evar _ as e1], _) when has_subst e1 ->
     let nctx = appctx (eapp ("TLA.isASeq", [x])) in
     do_substitutions e1 (elam (x, "", nctx)) g

  | Eapp ("TLA.DOMAIN", [Evar _ as e1], _) when has_subst e1 ->
     let nctx = appctx (eapp ("TLA.DOMAIN", [x])) in
     do_substitutions e1 (elam (x, "", nctx)) g

  | Eapp (("$notequiv" | "TLA.cond" | "TLA.CASE"), _, _) -> []

  | Eapp (f, args, _) ->
     let rec loop leftarg rightarg =
       match rightarg with
       | [] -> []
       | h::t ->
          let e1 = eapp (f, List.rev_append leftarg (x :: t)) in
          let newctx = appctx e1 in
          let rw = newnodes_subst x newctx h g in
          if rw <> [] then rw
          else loop (h::leftarg) t
     in
     loop [] args
  | _ -> []
;;

let newnodes_subst e g =
  let x = Expr.newvar () in
  newnodes_subst x x e g
;;

let rec mk_case_branches ctx l cond =
  match l with
  | [] -> [ [cond] ]
  | [e] -> [ [cond; ctx e] ]
  | c :: e :: t -> [c; ctx e] :: mk_case_branches ctx t (eand (enot (c), cond))
;;

let apply f e =
  match f with
  | Elam (v, _, b, _) -> Expr.substitute [(v, e)] b
  | _ -> assert false
;;

let has_ex e =
  match e with
  | Etau (v, t, (Enot (p, _) as np), _) ->
     Index.member (eex (v, t, np)) || Index.member (enot (eall (v, t, p)))
  | Etau (v, t, p, _) -> Index.member (eex (v, t, p))
  | _ -> assert false
;;

let rec get_nat_const e accu =
  match e with
  | Evar (s, _) ->
     begin try accu + int_of_string s
     with Failure _ -> raise (Invalid_argument "get_nat_const")
     end
  | Eapp ("TLA.fapply", [Evar ("TLA.Succ", _); e1], _) ->
     get_nat_const e1 (accu + 1)
  | _ -> raise (Invalid_argument "get_nat_const")
;;

let is_in_1_to e max =
  try
    let n = get_nat_const e 0 in
    0 < n && n <= max
  with Invalid_argument _ -> false
;;

let rewrites in_expr x ctx e mknode =
  let lamctx = elam (x, "", ctx) in
  let appctx e = substitute [(x, e)] ctx in
  let mk_boolcase_1 name e1 =
    let h1a = eapp ("=", [e; etrue]) in
    let h1b = appctx (etrue) in
    let h2a = eapp ("=", [e; efalse]) in
    let h2b = appctx (efalse) in
    mknode ("boolcase_" ^ name) [appctx e; h1a; h1b; h2a; h2b; lamctx; e1]
           [] [| [h1a; h1b]; [h2a; h2b] |]
  in
  let mk_boolcase_2 name e1 e2 =
    let h1a = eapp ("=", [e; etrue]) in
    let h1b = appctx (etrue) in
    let h2a = eapp ("=", [e; efalse]) in
    let h2b = appctx (efalse) in
    mknode ("boolcase_" ^ name) [appctx e; h1a; h1b; h2a; h2b; lamctx; e1; e2]
           [] [| [h1a; h1b]; [h2a; h2b] |]
  in
  let mk_eq_nodes lamctx heads e =
    let appctx x = apply lamctx x in
    let good_head x =
      match x with
      | Eapp (hd, _, _) -> heads = [] || List.mem hd heads
      | Evar (hd, _) -> heads = [] || List.mem hd heads
      | _ -> false
    in
    let lr = List.filter good_head (Index.find_eq_lr e) in
    let rl = List.filter good_head (Index.find_eq_rl e) in
    let rew_lr e2 =
      let h = appctx e2 in
      let c2 = eapp ("=", [e; e2]) in
      mknode ("rewrite_lr") [lamctx; e; e2] [c2] [| [h] |]
    in
    let rew_rl e2 =
      let h = appctx e2 in
      let c2 = eapp ("=", [e2; e]) in
      mknode ("rewrite_rl") [lamctx; e; e2] [c2] [| [h] |]
    in
    List.flatten (List.map rew_lr lr @ List.map rew_rl rl)
  in
  match e with
  | _ when in_expr && Index.member e ->
     let h1 = appctx (etrue) in
     mknode "trueistrue" [appctx e; e; h1; lamctx; e] [e] [| [h1] |]
  | Eapp ("$notequiv", [e1; e2], _) -> []
  | Evar (f, _) when in_expr && Index.has_def f ->
     let (d, params, body) = Index.get_def f in
     if params = [] then begin
       let unfolded = appctx body in
       mknode "definition" [appctx e; unfolded; e] [] [| [unfolded] |]
     end else
       []
  | Eapp (f, args, _) when in_expr && Index.has_def f ->
     let (d, params, body) = Index.get_def f in
     if List.length params = List.length args then begin
       let s = List.combine params args in
       let unfolded = appctx (substitute_2nd s body) in
       mknode "definition" [appctx e; unfolded; e] [] [| [unfolded] |]
     end else
       []
  | Eapp ("TLA.fapply", [Eapp ("TLA.Fcn", [s; Elam (v, _, b, _) as l], _); a], _)
  -> let h1 = enot (eapp ("TLA.in", [a; s])) in
     let h2 = appctx (Expr.substitute [(v, a)] b) in
     mknode "fapplyfcn" [appctx e; h1; h2; lamctx; s; l; a] [] [| [h1]; [h2] |]
  | Eapp ("TLA.fapply", [Eapp ("TLA.except", [f; v; e1], _); w], _) ->
     let indom = eapp ("TLA.in", [w; eapp ("TLA.DOMAIN", [f])]) in
     let h1a = indom in
     let h1b = eapp ("=", [v; w]) in
     let h1c = appctx e1 in
     let h2a = indom in
     let h2b = enot (eapp ("=", [v; w])) in
     let h2c = appctx (eapp ("TLA.fapply", [f; w])) in
     let h3 = enot indom in
     mknode "fapplyexcept" [appctx e; h1a; h1b; h1c; h2a; h2b; h2c; h3;
                            lamctx; f; v; e1; w]
            [] [| [h1a; h1b; h1c]; [h2a; h2b; h2c]; [h3] |]
  | Eapp ("TLA.fapply", [Eapp ("TLA.tuple", args, _); n], _)
    when is_in_1_to n (List.length args) ->
     let newe = List.nth args (get_nat_const n (-1)) in
     let h1 = appctx (newe) in
     mknode "tuple_access" [appctx e; h1; lamctx; e; newe] [] [| [h1] |]
  | Eapp ("TLA.fapply", [Eapp ("TLA.record", args, _); l], _) ->
     begin try
       let l_args = mk_pairs args in
       let newe = List.assq l l_args in
       let h1 = appctx (newe) in
       mknode "record_access" [appctx e; h1; lamctx; e; newe] [] [| [h1] |]
     with Not_found -> []
     end
(* ***
  | Eapp ("TLA.fapply", [f; a], _) ->
     let x = newvar () in
     let c = elam (x, "", appctx (eapp ("TLA.fapply", [x; a]))) in
     let result =
       mk_eq_nodes c ["TLA.Fcn"; "TLA.except"; "TLA.tuple"; "TLA.record"] f
     in
*** *)
  | Eapp ("TLA.DOMAIN", [Eapp ("TLA.Fcn", [s; l], _)], _) ->
     let h1 = appctx (s) in
     mknode "domain_fcn" [appctx e; h1; lamctx; s; l] [] [| [h1] |]
  | Eapp ("TLA.DOMAIN", [Eapp ("TLA.except", [f; v; e1], _)], _) ->
     let h1 = appctx (eapp ("TLA.DOMAIN", [f])) in
     mknode "domain_except" [appctx e; h1; lamctx; f; v; e1] [] [| [h1] |]
  | Eapp ("TLA.DOMAIN", [Eapp ("TLA.record", args, _)], _) ->
     let lbls = eapp ("TLA.set", List.map fst (mk_pairs args)) in
     let h1 = appctx lbls in
     mknode "record_domain" [appctx e; h1; lamctx; e; lbls] [] [| [h1] |]
  | Eapp ("TLA.DOMAIN", [f], _) ->
     let x = newvar () in
     let c = elam (x, "", appctx (eapp ("TLA.DOMAIN", [x]))) in
     mk_eq_nodes c ["TLA.Fcn"; "TLA.except"; "TLA.record"] f
  | Enot (e1, _) when in_expr -> mk_boolcase_1 "not" e1
  | Eand (e1, e2, _) when in_expr -> mk_boolcase_2 "and" e1 e2
  | Eor (e1, e2, _) when in_expr -> mk_boolcase_2 "or" e1 e2
  | Eimply (e1, e2, _) when in_expr -> mk_boolcase_2 "imply" e1 e2
  | Eequiv (e1, e2, _) when in_expr -> mk_boolcase_2 "equiv" e1 e2
  | Eapp ("=", [e1; e2], _) when in_expr -> mk_boolcase_2 "equal" e1 e2
  | Eall (v, t, p, _) when in_expr -> mk_boolcase_1 "all" (elam (v, t, p))
  | Eex (v, t, p, _) when in_expr -> mk_boolcase_1 "ex" (elam (v, t, p))

  | Eapp ("TLA.cond", [Etrue; e1; e2], _) ->
     let h1 = appctx (e1) in
     mknode "iftrue" [appctx e; h1; lamctx; e1; e2] [] [| [h1] |]
  | Eapp ("TLA.cond", [Efalse; e1; e2], _) ->
     let h1 = appctx (e2) in
     mknode "iffalse" [appctx e; h1; lamctx; e1; e2] [] [| [h1] |]
  | Eapp ("TLA.cond", [e0; e1; e2], _) ->
     let h1a = e0 in
     let h1b = appctx (e1) in
     let h2a = enot (e0) in
     let h2b = appctx (e2) in
     mknode "ifthenelse" [appctx e; h1a; h1b; h2a; h2b; lamctx; e0; e1; e2] []
            [| [h1a; h1b]; [h2a; h2b] |]
  | Eapp ("TLA.CASE", args, _) ->
     let branches = mk_case_branches appctx args etrue in
     let c = appctx e in
     mknode "case" (c :: lamctx :: List.flatten branches) [c]
            (Array.of_list branches)
  | Etau (v, t, b, _) when not (has_ex e) ->
     let h1 = eex (v, t, b) in
     let h2 = enot (h1) in
     mknode "cut" [h1] [] [| [h1]; [h2] |]
  | Eapp ("TLA.Len", [Eapp ("TLA.tuple", args, _)], _) ->
     let r = mk_nat (List.length args) in
     let h1 = appctx r in
     mknode "tuple_len" [appctx e; h1; lamctx; e; r] [] [| [h1] |]
  | Eapp ("TLA.Len", [s], _) ->
     let x = newvar () in
     let c = elam (x, "", appctx (eapp ("TLA.Len", [x]))) in
     mk_eq_nodes c ["TLA.tuple"] s

  | Eapp ("TLA.isASeq", [s], _) ->
     let x = newvar () in
     let c = elam (x, "", appctx (eapp ("TLA.isASeq", [x]))) in
     mk_eq_nodes c ["TLA.tuple"] s
  | Eapp ("TLA.in", [a; s], _) ->
     let x = newvar () in
     let c = elam (x, "", appctx (eapp ("TLA.in", [a; x]))) in
     let heads =
       match s with
       | Evar _ -> []  (* always replace a var; see prove.ml *)
       | _ -> ["TLA.emptyset"; "TLA.upair"; "TLA.addElt"; "TLA.set";
                    "TLA.SUBSET"; "TLA.UNION"; "TLA.cup"; "TLA.cap";
                    "TLA.setminus"; "TLA.subsetOf"; "TLA.setOfAll";
                    "TLA.FuncSet"; "TLA.Product"]
     in
     mk_eq_nodes c heads s
  | Eapp ("TLA.isAFcn", [s], _) ->
     let x = newvar () in
     let c = elam (x, "", appctx (eapp ("TLA.isAFcn", [x]))) in
     mk_eq_nodes c ["TLA.Fcn"; "TLA.except"; "TLA.oneArg"; "TLA.extend";
                    "TLA.record"] s

  | _ -> []
;;

let rec find_rewrites in_expr x ctx e mknode =
  let local = rewrites in_expr x ctx e mknode in
  match e with
  | _ when local <> [] -> local
  | Eapp ("$notequiv", [e1; e2], _) -> []
  | Eapp (p, args, _) ->
     let rec loop leftarg rightarg =
       match rightarg with
       | [] -> []
       | h::t ->
          let e1 = eapp (p, List.rev_append leftarg (x :: t)) in
          let newctx = substitute [(x, e1)] ctx in
          begin match find_rewrites true x newctx h mknode with
          | [] -> loop (h::leftarg) t
          | l -> l
          end
     in
     loop [] args
  | Enot (e1, _) ->
     find_rewrites false x (substitute [(x, enot x)] ctx) e1 mknode
  | _ -> []
;;

let newnodes_rewrites e g =
  let mknode name args add_con branches =
    match name, args with
    | "definition", [folded; unfolded; Evar (f, _)] ->
       let (def, params, body) = Index.get_def f in
       [ Node {
         nconc = e :: add_con;
         nrule = Definition (def, folded, unfolded);
         nprio = Arity;
         ngoal = g;
         nbranches = branches;
       }]
    | "definition", [folded; unfolded; Eapp (f, args, _)] ->
       let (def, params, body) = Index.get_def f in
       [ Node {
         nconc = e :: add_con;
         nrule = Definition (def, folded, unfolded);
         nprio = Arity;
         ngoal = g;
         nbranches = branches;
       }]
    | "definition", _ -> assert false
    | "cut", [h] ->
       [ Node {
         nconc = add_con;
         nrule = Cut (h);
         nprio = Arity;
         ngoal = g;
         nbranches = branches;
       }]
    | "cut", _ -> assert false
    | "rewrite_lr", [p; e1; e2] ->
       [ Node {
         nconc = e :: add_con;
         nrule = CongruenceLR (p, e1, e2);
         nprio = Arity;
         ngoal = g;
         nbranches = branches;
       }]
    | "rewrite_lr", _ -> assert false
    | "rewrite_rl", [p; e1; e2] ->
       [ Node {
         nconc = e :: add_con;
         nrule = CongruenceRL (p, e1, e2);
         nprio = Arity;
         ngoal = g;
         nbranches = branches;
       }]
    | "rewrite_rl", _ -> assert false
    | _ ->
       [ Node {
         nconc = e :: add_con;
         nrule = Ext ("tla", name, args);
         nprio = Arity;
         ngoal = g;
         nbranches = branches;
       }]
       @ (if name = "ifthenelse" then [Stop] else [])
  in
  let x = Expr.newvar () in
  find_rewrites false x x e mknode
;;

let newnodes e g _ =
  newnodes_prop e g @ newnodes_rewrites e g
(*  @ newnodes_subst e g *)
  @ newnodes_prop_eq e g @ newnodes_eq_prop_l e g @ newnodes_eq_prop_r e g
  @ newnodes_inst_bounded e g
;;

let make_inst m term g = assert false;;

let rec split_case_branches l =
  match l with
  | [] -> []
  | [e] -> [ [e] ]
  | c :: e :: t -> [c; e] :: split_case_branches t
;;

let to_llargs r =
  let alpha r =
    match r with
    | Ext (_, name, c :: h1 :: h2 :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1; h2] ])
    | _ -> assert false
  in
  let beta r =
    match r with
    | Ext (_, name, c :: h1 :: h2 :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1]; [h2] ])
    | _ -> assert false
  in
  let beta2 r =
    match r with
    | Ext (_, name, c :: h1a :: h1b :: h2a :: h2b :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1a; h1b]; [h2a; h2b] ])
    | _ -> assert false
  in
  let cut12 r =
    match r with
    | Ext (_, name, h1 :: h2a :: h2b :: args) ->
       ("zenon_" ^ name, args, [], [ [h1]; [h2a; h2b] ])
    | _ -> assert false
  in
  let single r =
    match r with
    | Ext (_, name, c :: h :: args) -> ("zenon_" ^ name, args, [c], [ [h] ])
    | _ -> assert false
  in
  let close r =
    match r with
    | Ext (_, name, c :: args) -> ("zenon_" ^ name, args, [c], [])
    | _ -> assert false
  in
  let binsingle r =
    match r with
    | Ext (_, name, c1 :: c2 :: h :: args) ->
        ("zenon_" ^ name, args, [c1; c2], [[h]])
    | _ -> assert false
  in
  let binbeta r =
    match r with
    | Ext (_, name, c1 :: c2 :: h1 :: h2 :: args) ->
       ("zenon_" ^ name, args, [c1; c2], [ [h1]; [h2] ])
    | _ -> assert false
  in
  match r with
  | Ext (_, "in_emptyset", [c; e1]) -> ("zenon_in_emptyset", [e1], [c], [])
  | Ext (_, "in_nat_0", [c]) -> ("zenon_in_nat_0", [], [c], [])
  | Ext (_, "in_nat_1", [c]) -> ("zenon_in_nat_1", [], [c], [])
  | Ext (_, "in_nat_2", [c]) -> ("zenon_in_nat_2", [], [c], [])
  | Ext (_, "in_upair", _) -> beta r
  | Ext (_, "notin_upair", _) -> alpha r
  | Ext (_, "in_cup", _) -> beta r
  | Ext (_, "notin_cup", _) -> alpha r
  | Ext (_, "in_cap", _) -> alpha r
  | Ext (_, "notin_cap", _) -> beta r
  | Ext (_, "in_setminus", _) -> alpha r
  | Ext (_, "notin_setminus", _) -> beta r
  | Ext (_, "in_subsetof", _) -> alpha r
  | Ext (_, "notin_subsetof", _) -> beta r
  | Ext (_, "in_funcset", [c; h1; h2; h3; f; a; b]) ->
     ("zenon_in_funcset", [f; a; b], [c], [ [h1; h2; h3] ])
  | Ext (_, "except_notin_funcset", [c; h1; h2; f1; v; e1; a; b]) ->
     ("zenon_except_notin_funcset", [f1; v; e1; a; b], [c], [ [h1]; [h2] ])
  | Ext (_, "notin_funcset", [c; h1; h2; h3; f; a; b]) ->
     ("zenon_notin_funcset", [f; a; b], [c], [ [h1]; [h2]; [h3] ])
  | Ext (_, "trueistrue", [c1; c2; h1; ctx; e1]) ->
     ("zenon_trueistrue", [ctx; e1], [c1; c2], [ [h1] ])
  | Ext (_, "fapplyfcn", _) -> beta r
  | Ext (_, "fapplyexcept", [c; h1a; h1b; h1c; h2a; h2b; h2c; h3;
                             ctx; f; v; e1; w]) ->
     ("zenon_fapplyexcept", [ctx; f; v; e1; w], [c],
      [ [h1a; h1b; h1c]; [h2a; h2b; h2c]; [h3] ])
  | Ext (_, "boolcase_not", _) -> beta2 r
  | Ext (_, "boolcase_and", _) -> beta2 r
  | Ext (_, "boolcase_or", _) -> beta2 r
  | Ext (_, "boolcase_imply", _) -> beta2 r
  | Ext (_, "boolcase_equiv", _) -> beta2 r
  | Ext (_, "boolcase_equal", _) -> beta2 r
  | Ext (_, "boolcase_all", _) -> beta2 r
  | Ext (_, "boolcase_ex", _) -> beta2 r
  | Ext (_, "notisafcn_fcn", _) -> close r
  | Ext (_, "notisafcn_except", _) -> close r
  | Ext (_, "notisafcn_onearg", _) -> close r
  | Ext (_, "notisafcn_extend", _) -> close r
  | Ext (_, "ifthenelse", _) -> beta2 r
  | Ext (_, "notequalchoose", _) -> cut12 r
  | Ext (_, "case", c :: p :: args) ->
     ("zenon_case", [p], [c], split_case_branches args)
  | Ext (_, ("p_eq_l" | "p_eq_r" | "np_eq_l" | "np_eq_r"), _) -> binbeta r
  | Ext (_, ("all_in" | "notex_in"), _) -> binsingle r

  | Ext (_, "cup_subseteq", _) -> alpha r
  | Ext (_, "not_cup_subseteq", _) -> beta r
  | Ext (_, "subseteq_cap", _) -> alpha r
  | Ext (_, "not_subseteq_cap", _) -> beta r

  | Ext (_, "tuple_eq_match", c :: hs) ->
     ("zenon_tuple_eq_match", [], [c], [ hs ])
  | Ext (_, "tuple_eq_mismatch", _) -> close r
  | Ext (_, "in_product", c :: e1 :: e2 :: hs) ->
     ("zenon_in_product", [e1; e2], [c], [ hs ])
  | Ext (_, "notin_product", c :: e1 :: e2 :: hs) ->
     ("zenon_notin_product", [e1; e2], [c], List.map (fun x -> [x]) hs)
  | Ext (_, "tuple_notisaseq", _) -> close r

  | Ext (_, "record_eq_match", c :: hs) ->
     ("zenon_record_eq_match", [], [c], [ hs ])
  | Ext (_, "record_neq_match", c :: hs) ->
     ("zenon_record_neq_match", [], [c], List.map (fun x -> [x]) hs)
  | Ext (_, "record_eq_mismatch", _) -> close r
  | Ext (_, "neq_record", c :: e1 :: e2 :: hs) ->
     ("zenon_neq_record", [e1; e2], [c], List.map (fun x -> [x]) hs)
  | Ext (_, "record_neq", c :: e1 :: e2 :: hs) ->
     ("zenon_record_neq", [e1; e2], [c], List.map (fun x -> [x]) hs)
  | Ext (_, "in_recordset", c :: e1 :: e2 :: hs) ->
     ("zenon_in_recordset", [e1; e2], [c], [ hs ])
  | Ext (_, "notin_recordset", c :: e1 :: e2 :: hs) ->
     ("zenon_notin_recordset", [e1; e2], [c], List.map (fun x -> [x]) hs)
  | Ext (_, "record_notisafcn", _) -> close r

  | Ext (_, name, _) -> single r
  | _ -> assert false
;;

let is_simple r =
  match r with
  | Ext (_, "in_addElt", _) -> false
  | Ext (_, "notin_addElt", _) -> false
  | _ -> true
;;

let to_llproof tr_expr mlp args =
  match mlp.mlrule with
  | Ext (_, "in_addElt", [c; x; s]) ->
     let subexts = Array.to_list args in
     let tre = tr_expr in
     let trl l = List.map tr_expr l in
     let rec mkproof s subexts myconc =
       match s, subexts with
       | Evar ("TLA.emptyset", _), _ ->
         let tconc = tre (eapp ("TLA.in", [x; s])) in
         let n0 = {
           Llproof.conc = trl myconc;
           Llproof.rule = Llproof.Rextension ("", "zenon_in_emptyset",
                                              [tre x], [tconc], []);
           Llproof.hyps = [];
         } in
         (n0, [])
       | Eapp ("TLA.addElt", [y; s1], _), ((sub, ext) :: t) ->
          let concl = eapp ("TLA.in", [x; s]) in
          let h1 = eapp ("=", [x; y]) in
          let h2 = eapp ("TLA.in", [x; s1]) in
          let (sub1, ext1) = mkproof s1 t (h2 :: myconc) in
          let extras = Expr.diff (Expr.union ext ext1) myconc in
          let n0 = {
            Llproof.conc = trl (extras @@ myconc);
            Llproof.rule = Llproof.Rextension ("", "zenon_in_addElt",
                                               trl [x; y; s1], [tre concl],
                                               [ [tre h1]; [tre h2] ]);
            Llproof.hyps = [sub; sub1];
          } in
          (n0, extras)
        | _, [subext] -> subext
        | _ -> assert false
     in
     mkproof s subexts mlp.mlconc
  | Ext (_, "in_set", [c; x; s]) ->
     let subexts = Array.to_list args in
     let tre = tr_expr in
     let trl l = List.map tr_expr l in
     let rec mkproof s subexts myconc =
       match s, subexts with
       | Eapp ("TLA.set", [], _), [] ->
         let tconc = tre (eapp ("TLA.in", [x; s])) in
         let n0 = {
           Llproof.conc = trl myconc;
           Llproof.rule = Llproof.Rextension ("", "zenon_in_emptyset",
                                              [tre x], [tconc], []);
           Llproof.hyps = [];
         } in
         (n0, [])
       | Eapp ("TLA.set", y :: l1, _), ((sub, ext) :: t) ->
          let s1 = eapp ("TLA.set", l1) in
          let concl = eapp ("TLA.in", [x; s]) in
          let h1 = eapp ("=", [x; y]) in
          let h2 = eapp ("TLA.in", [x; s1]) in
          let (sub1, ext1) = mkproof s1 t (h2 :: myconc) in
          let extras = Expr.diff (Expr.union ext ext1) myconc in
          let n0 = {
            Llproof.conc = trl (extras @@ myconc);
            Llproof.rule = Llproof.Rextension ("", "zenon_in_addElt",
                                               trl [x; y; s1], [tre concl],
                                               [ [tre h1]; [tre h2] ]);
            Llproof.hyps = [sub; sub1];
          } in
          (n0, extras)
        | _ -> assert false
     in
     mkproof s subexts mlp.mlconc
  | Ext (_, "notin_addElt", [c; x; s]) ->
     let (sub, ext) =
       match args with
       | [| (sub, ext) |] -> (sub, ext)
       | _ -> assert false
     in
     let tre = tr_expr in
     let trl l = List.map tr_expr l in
     let rec mkproof s myconc =
       match s with
       | Eapp ("TLA.addElt", [y; s1], _) ->
          let concl = enot (eapp ("TLA.in", [x; s])) in
          let h1 = enot (eapp ("=", [x; y])) in
          let h2 = enot (eapp ("TLA.in", [x; s1])) in
          let (sub1, ext1) = mkproof s1 (h1 :: h2 :: myconc) in
          let extras = Expr.diff ext1 myconc in
          let n0 = {
            Llproof.conc = trl (extras @@ myconc);
            Llproof.rule = Llproof.Rextension ("", "zenon_notin_addElt",
                                               trl [x; y; s1], [tre concl],
                                               [ trl [h1; h2] ]);
            Llproof.hyps = [sub1];
          } in
          (n0, extras)
       | _ -> (sub, ext)
     in
     mkproof s mlp.mlconc
  | Ext (_, "notin_set", [c; x; s]) ->
     let (sub, ext) =
       match args with
       | [| (sub, ext) |] -> (sub, ext)
       | _ -> assert false
     in
     let tre = tr_expr in
     let trl l = List.map tr_expr l in
     let rec mkproof s myconc =
       match s with
       | Eapp ("TLA.set", y :: l1, _) ->
          let s1 = eapp ("TLA.set", l1) in
          let concl = enot (eapp ("TLA.in", [x; s])) in
          let h1 = enot (eapp ("=", [x; y])) in
          let h2 = enot (eapp ("TLA.in", [x; s1])) in
          let (sub1, ext1) = mkproof s1 (h1 :: h2 :: myconc) in
          let extras = Expr.diff ext1 myconc in
          let n0 = {
            Llproof.conc = trl (extras @@ myconc);
            Llproof.rule = Llproof.Rextension ("", "zenon_notin_addElt",
                                               trl [x; y; s1], [tre concl],
                                               [ trl [h1; h2] ]);
            Llproof.hyps = [sub1];
          } in
          (n0, extras)
       | _ -> (sub, ext)
     in
     mkproof s mlp.mlconc
  | Ext (_, "notequivdef", _) ->
     begin match args with
     | [| a |] -> a
     | _ -> assert false
     end
  | _ ->
     let (name, meta, con, hyps) = to_llargs mlp.mlrule in
     let tmeta = List.map tr_expr meta in
     let tcon = List.map tr_expr con in
     let thyps = List.map (List.map tr_expr) hyps in
     let (subs, exts) = List.split (Array.to_list args) in
     let ext = List.fold_left Expr.union [] exts in
     let extras = Expr.diff ext mlp.mlconc in
     let nn = {
         Llproof.conc = List.map tr_expr (extras @@ mlp.mlconc);
         Llproof.rule = Llproof.Rextension ("", name, tmeta, tcon, thyps);
         Llproof.hyps = subs;
       }
     in (nn, extras)
;;

let built_in_defs =
  [
    Def (DefReal ("subset_def", "TLA.subseteq", [evar "A"; evar "B"],
       eapp ("TLA.bAll", [evar "A";
                   elam (evar "x", "",
                         eapp ("TLA.in", [evar "x"; evar "B"]))]), None));
    Def (DefReal ("bAll_def", "TLA.bAll", [evar "S"; evar "P"],
       eall (evar "x", "",
             eimply (eapp ("TLA.in", [evar "x"; evar "S"]),
                     eapp ("P", [evar "x"]))), None));
    Def (DefReal ("bEx_def", "TLA.bEx", [evar "S"; evar "P"],
       eex (evar "x", "",
            eand (eapp ("TLA.in", [evar "x"; evar "S"]),
                  eapp ("P", [evar "x"]))), None));
    Def (DefReal ("bChoose_def", "TLA.bChoice", [evar "S"; evar "P"],
       etau (evar "x", "",
            eand (eapp ("TLA.in", [evar "x"; evar "S"]),
                  eapp ("P", [evar "x"]))), None));
    Def (DefReal ("prod_def", "TLA.prod", [evar "A"; evar "B"],
       eapp ("TLA.Product", [eapp ("TLA.tuple", [evar "A"; evar "B"])]), None));
  ]
;;

let preprocess l = built_in_defs @ l;;

let add_phrase p = ();;

let rec pp_expr e =
  match e with
  | Evar _ -> e
  | Emeta _ -> assert false
  | Eapp ("$notequiv", [e1; e2], _) -> enot (eequiv (pp_expr e1, pp_expr e2))
  | Eapp ("$notequiv", _, _) -> assert false
  | Eapp (s, args, _) -> eapp (s, List.map pp_expr args)
  | Enot (e1, _) -> enot (pp_expr e1)
  | Eand (e1, e2, _) -> eand (pp_expr e1, pp_expr e2)
  | Eor (e1, e2, _) -> eor (pp_expr e1, pp_expr e2)
  | Eimply (e1, e2, _) -> eimply (pp_expr e1, pp_expr e2)
  | Eequiv (e1, e2, _) -> eequiv (pp_expr e1, pp_expr e2)
  | Etrue | Efalse -> e
  | Eall (v, t, e1, _) -> eall (pp_expr v, t, pp_expr e1)
  | Eex (v, t, e1, _) -> eex (pp_expr v, t, pp_expr e1)
  | Etau (v, t, e1, _) -> etau (pp_expr v, t, pp_expr e1)
  | Elam (v, t, e1, _) -> elam (pp_expr v, t, pp_expr e1)
;;

module LL = Llproof;;

let pp_rule r =
  match r with
  | LL.Rfalse | LL.Rnottrue -> r
  | LL.Raxiom (e) -> LL.Raxiom (pp_expr e)
  | LL.Rcut (e) -> LL.Rcut (pp_expr e)
  | LL.Rnoteq (e) -> LL.Rnoteq (pp_expr e)
  | LL.Reqsym (e1, e2) -> LL.Reqsym (pp_expr e1, pp_expr e2)
  | LL.Rnotnot (e) -> LL.Rnotnot (pp_expr e)
  | LL.Rconnect (op, e1, e2) -> LL.Rconnect (op, pp_expr e1, pp_expr e2)
  | LL.Rnotconnect (op, e1, e2) -> LL.Rnotconnect (op, pp_expr e1, pp_expr e2)
  | LL.Rex (e1, e2) -> LL.Rex (pp_expr e1, pp_expr e2)
  | LL.Rall (e1, e2) -> LL.Rall (pp_expr e1, pp_expr e2)
  | LL.Rnotex (e1, e2) -> LL.Rnotex (pp_expr e1, pp_expr e2)
  | LL.Rnotall (e1, e2) -> LL.Rnotall (pp_expr e1, pp_expr e2)
  | LL.Rpnotp (e1, e2) -> LL.Rpnotp (pp_expr e1, pp_expr e2)
  | LL.Rnotequal (e1, e2) -> LL.Rnotequal (pp_expr e1, pp_expr e2)
  | LL.RcongruenceLR (e1, e2, e3) ->
     LL.RcongruenceLR (pp_expr e1, pp_expr e2, pp_expr e3)
  | LL.RcongruenceRL (e1, e2, e3) ->
     LL.RcongruenceRL (pp_expr e1, pp_expr e2, pp_expr e3)
  | LL.Rdefinition (nm, id, args, body, recarg, e1, e2) ->
     LL.Rdefinition (nm, id, args, body, recarg, pp_expr e1, pp_expr e2)
  | LL.Rextension (ext, n, a, cs, hss) ->
     LL.Rextension (ext, n, List.map pp_expr a, List.map pp_expr cs,
                 List.map (List.map pp_expr) hss)
  | LL.Rlemma (n, args) -> LL.Rlemma (n, List.map pp_expr args)
;;

let rec pp_prooftree t = {
  LL.conc = List.map pp_expr t.LL.conc;
  LL.rule = pp_rule t.LL.rule;
  LL.hyps = List.map pp_prooftree t.LL.hyps;
};;

let pp_lemma l = {
  LL.name = l.LL.name;
  LL.params = List.map (fun (t, e) -> (t, pp_expr e)) l.LL.params;
  LL.proof = pp_prooftree l.LL.proof;
};;

let postprocess p = List.map pp_lemma p;;

let declare_context_coq oc = ();;

let p_rule_coq oc r = assert false;;

let predef () =
  tla_set_constructors @ tla_fcn_constructors @ tla_other_symbols
;;

Extension.register {
  Extension.name = "tla";
  Extension.newnodes = newnodes;
  Extension.make_inst = make_inst;
  Extension.add_formula = add_formula;
  Extension.remove_formula = remove_formula;
  Extension.preprocess = preprocess;
  Extension.add_phrase = add_phrase;
  Extension.postprocess = postprocess;
  Extension.to_llproof = to_llproof;
  Extension.declare_context_coq = declare_context_coq;
  Extension.p_rule_coq = p_rule_coq;
  Extension.predef = predef;
};;
