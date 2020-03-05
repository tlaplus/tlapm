(*  Copyright 2004 INRIA  *)

(* Extension for trees of equivalences and negations. *)

(* TODO:
   Si la formule courante a beaucoup de points communs avec une
   des hypotheses, faire un cut sur l'equivalence des deux.
   Faire attention, dans la branche negative, de ne pas combiner
   les deux, mais de faire un equiv normal, qui ferme tout de suite.
*)

open Expr;;
open Misc;;
open Mlproof;;
open Node;;

let rec get_leaves e ((neg, lvs) as accu) =
  match e with
  | Etrue -> accu
  | Efalse -> (not neg, lvs)
  | Eequiv (f, g, _) -> get_leaves f (get_leaves g accu)
  | Enot (f, _) -> get_leaves f (not neg, lvs)
  | _ -> (neg, e::lvs)
;;

let rec remove_pairs l =
  match l with
  | x :: (y :: tt as t) ->
      if Expr.equal x y
      then remove_pairs tt
      else x :: remove_pairs t
  | _ -> l
;;

let rec make_list l =
  match l with
  | [] -> etrue
  | h::t -> eequiv (make_list t, h)
;;

let newnodes e g _ =
  match e with
  | Eequiv _ | Enot (Eequiv _, _) ->
      let (neg, leaves) = get_leaves e (false, []) in
      let sorted = List.fast_sort Expr.compare leaves in
      let reduced = remove_pairs sorted in
      if List.length reduced < List.length leaves then
        let branches =
          if neg then [| [enot (make_list reduced)] |]
          else [| [make_list reduced] |]
        in
        [ Node {
          nconc = [e];
          nrule = Ext ("equiv", "pairs", [e]);
          nprio = Arity;
          ngoal = g;
          nbranches = branches;
        }; Stop ]
      else
        []
  | _ -> []
;;

let make_inst m term g = assert false;;

type node = {
  nconc : Expr.expr;
  nrule : string;
  nargs : Expr.expr list;
  nhyp : Expr.expr;
};;

let chain_nodes tr_prop mlconc init l =
  let f n0 n1 =
    let conc = Expr.diff [n1.nconc] mlconc in
    {
      Llproof.conc = List.map tr_prop (conc @@ mlconc);
      Llproof.rule =
        Llproof.Rextension ("", n1.nrule, List.map tr_prop n1.nargs,
                            [tr_prop n1.nconc], [ [tr_prop n1.nhyp] ]);
      Llproof.hyps = [n0];
    }
  in
  List.fold_left f init l
;;

let mknode conc ru args hyp = {
  nconc = conc;
  nrule = "zenon_equiv_" ^ ru;
  nargs = args;
  nhyp = hyp;
};;

let init_0 (e, nodes) =
  let res = eequiv (etrue, eequiv (e, etrue)) in
  let node = mknode e "init_0" [e] res in
  (res, node :: nodes)
;;

let rec make_lists (ee, nodes) =
  match ee with
  | Eequiv (k, Enot (Enot (a, _), _), _) ->
      let res = eequiv (k, a) in
      let node = mknode ee "init_4" [k; a] res in
      make_lists (res, node :: nodes)
  | Eequiv (k, Enot (Eequiv (a, b, _), _), _) ->
      let res = eequiv (k, eequiv (a, enot (b))) in
      let node = mknode ee "init_3" [k; a; b] res in
      make_lists (res, node :: nodes)
  | Eequiv (k, Eequiv (Enot (a, _), b, _), _) ->
      let res = eequiv (k, eequiv (a, enot (b))) in
      let node = mknode ee "init_5" [k; a; b] res in
      make_lists (res, node :: nodes)
  | Eequiv (k, Eequiv (Etrue, b, _), _) ->
      let res = eequiv (k, b) in
      let node = mknode ee "init_8" [k; b] res in
      make_lists (res, node :: nodes)
  | Eequiv (k, Eequiv (Efalse, b, _), _) ->
      let res = eequiv (k, enot (b)) in
      let node = mknode ee "init_9" [k; b] res in
      make_lists (res, node :: nodes)
  | Eequiv (k, Eequiv (Eequiv (a, b, _), c, _), _) ->
      let res = eequiv (k, eequiv (a, eequiv (b, c))) in
      let node = mknode ee "init_2" [k; a; b; c] res in
      make_lists (res, node :: nodes)
  | Eequiv (k, Eequiv (a, b, _), _) ->
      let res = eequiv (eequiv (k, eequiv (etrue, a)), b) in
      let node = mknode ee "init_1" [k; a; b] res in
      make_lists (res, node :: nodes)
  | Eequiv (k, Enot (Etrue, _), _) ->
      let res = eequiv (eequiv (k, etrue), eequiv (efalse, etrue)) in
      let node = mknode ee "init_7" [k] res in
      (res, node :: nodes)
  | Eequiv (k, Etrue, _) ->
      let res = eequiv (eequiv (k, etrue), eequiv (etrue, etrue)) in
      let node = mknode ee "init_6" [k] res in
      (res, node :: nodes)
  | _ -> assert false
;;

let simplify (ee, nodes) =
  match ee with
  | Eequiv (l, Eequiv (m, Eequiv (Eequiv (n, a, _), b, _), _), _)
    when Expr.equal a b ->
      assert (not true);   (* should not happen if merge_simplify is used *)
      let res = eequiv (l, eequiv (m, n)) in
      let node = mknode ee "simplify" [a; l; m; n] res in
      (res, node :: nodes)
  | _ -> (ee, nodes)
;;

let rec reverse (ee, nodes) =
  match ee with
  | Eequiv (l, Eequiv (Eequiv (a, b, _), Eequiv (c, d, _), _), _) ->
      let res = eequiv (l, eequiv (eequiv (a, eequiv (b, d)), c)) in
      let node = mknode ee "reverse" [l; a; b; c; d] res in
      reverse (res, node :: nodes)
  | Eequiv (l, Eequiv (Eequiv (a, b, _), Etrue, _), _) ->
      (ee, nodes)
  | _ -> assert false
;;

let rec sort (ee, nodes) =
  match ee with
  | Eequiv (Etrue, Eequiv (Eequiv (Etrue, q, _), Etrue, _), _) ->
      let res = q in
      let node = mknode ee "finish_0" [q] res in
      (res, node :: nodes)
  | Eequiv (Etrue, Eequiv (Eequiv (Efalse, q, _), Etrue, _), _) ->
      let res = enot (q) in
      let node = mknode ee "finish_1" [q] res in
      (res, node :: nodes)
  | Eequiv (Efalse, Eequiv (Eequiv (Etrue, q, _), Etrue, _), _) ->
      let res = enot (q) in
      let node = mknode ee "finish_2" [q] res in
      (res, node :: nodes)
  | Eequiv ((Etrue | Efalse) as a, Eequiv (q, Etrue, _), _) ->
      let res = eequiv (q, eequiv (a, etrue)) in
      let node = mknode ee "outer_loop" [a; q] res in
      sort (res, node :: nodes)
  | Eequiv (Eequiv (Eequiv (l, Etrue, _), Etrue, _), Eequiv (a, b, _), _) ->
      let res = eequiv (l, eequiv (eequiv (a, etrue), b)) in
      let node = mknode ee "inner_loop" [l; a; b] res in
      sort (reverse (res, node :: nodes))
  | Eequiv (Eequiv ((Etrue | Efalse) as a, l, _), Eequiv (q, Etrue, _), _) ->
      let res = eequiv (a, eequiv (eequiv (q, l), etrue)) in
      let node = mknode ee "merge_1" [a; l; q] res in
      sort (res, node :: nodes)
  | Eequiv (Eequiv ((Eequiv (a, Eequiv (b, c, _), _) as x),
                    (Eequiv (d, e, _) as y), _),
            (Eequiv (f, g, _) as z), _)
   -> begin match Expr.compare c e with
      | 0 ->
          let res = eequiv (eequiv (eequiv (a, b), d), z) in
          let node = mknode ee "merge_simplify" [a; b; c; d; z] res in
          sort (res, node :: nodes)
      | x when x < 0 ->
          let res = eequiv (eequiv (eequiv (a, b), y),
                            eequiv (f, eequiv (g, c)))
          in
          let node = mknode ee "merge_left" [a; b; c; y; f; g] res in
          sort (simplify (res, node :: nodes))
      | _ ->
          let res = eequiv (eequiv (x, d), eequiv (f, eequiv (g, e))) in
          let node = mknode ee "merge_right" [x; d; e; f; g] res in
          sort (simplify (res, node :: nodes))
      end
  | Eequiv (Eequiv ((Eequiv (a, Etrue, _) as x), Eequiv (d, e, _), _),
            Eequiv (f, g, _), _)
   -> let res = eequiv (eequiv (x, d), eequiv (f, eequiv (g, e))) in
      let node = mknode ee "merge_right" [x; d; e; f; g] res in
      sort (simplify (res, node :: nodes))
  | Eequiv (Eequiv (Eequiv (a, Eequiv (b, c, _), _), (Etrue as y), _),
            Eequiv (f, g, _), _)
   -> let res = eequiv (eequiv (eequiv (a, b), y), eequiv (f, eequiv (g, c))) in
      let node = mknode ee "merge_left" [a; b; c; y; f; g] res in
      sort (simplify (res, node :: nodes))
  | _ -> assert false
;;

let ( ++ ) e f = f e;;

let to_llproof tr_prop tr_term mlp args =
  match (mlp.mlrule, args) with
  | Ext ("equiv", "pairs", [orig]), [| (subproof, extras) |] ->
      let final, nodes =
        (orig, [])
        ++ init_0
        ++ make_lists
        ++ sort
      in
      let node = chain_nodes tr_prop mlp.mlconc subproof nodes in
      (node, extras)
  | _ -> assert false
;;

let declare_context_coq oc =
  Printf.fprintf oc "Require Import zenon_equiv.\n";
;;

let p_rule_coq oc r = assert false;;

let predef () = [];;

Extension.register {
  Extension.name = "equiv";
  Extension.newnodes = newnodes;
  Extension.make_inst = make_inst;
  Extension.add_formula = (fun _ -> ());
  Extension.remove_formula = (fun _ -> ());
  Extension.preprocess = (fun x -> x);
  Extension.add_phrase = (fun _ -> ());
  Extension.postprocess = (fun x -> x);
  Extension.to_llproof = (fun tr_expr -> to_llproof tr_expr tr_expr);
  Extension.declare_context_coq = declare_context_coq;
  Extension.p_rule_coq = p_rule_coq;
  Extension.predef = predef;
};;
