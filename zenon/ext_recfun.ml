(*  Copyright 2009 INRIA  *)

(* Extension for recursive function definitions. *)

open Printf;;

open Expr;;
open Misc;;
open Mlproof;;
open Node;;
open Phrase;;

let newnodes e g _ = [];;

let make_inst m term g = assert false;;

let add_formula e = ();;
let remove_formula e = ();;

let preprocess l = l;;

let add_phrase p = ();;

let postprocess p = p;;

let to_llargs tr_expr r =
  match r with
  | Ext (_, "unfold", [p; a; b; eq]) ->
      let h = tr_expr (apply p b) in
      let c = tr_expr (apply p a) in
      ("zenon_recfun_unfold", [tr_expr p; tr_expr a; tr_expr b; tr_expr eq],
       [c], [ [h] ])
  | _ -> assert false
;;

let to_llproof tr_expr mlp args =
  let (name, meta, con, hyp) = to_llargs tr_expr mlp.mlrule in
  let (subs, exts) = List.split (Array.to_list args) in
  let ext = List.fold_left Expr.union [] exts in
  let extras = Expr.diff ext mlp.mlconc in
  let nn = {
      Llproof.conc = List.map tr_expr (extras @@ mlp.mlconc);
      Llproof.rule = Llproof.Rextension ("", name, meta, con, hyp);
      Llproof.hyps = subs;
    }
  in (nn, extras)
;;

let declare_context_coq oc = ();;

let p_rule_coq oc r = assert false;;

let predef () = [];;

Extension.register {
  Extension.name = "recfun";
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
