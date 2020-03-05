(*  Copyright 2004 INRIA  *)

open Mlproof;;
open Printf;;

type translator =
    (Expr.expr -> Expr.expr) ->
    Mlproof.proof -> (Llproof.prooftree * Expr.expr list) array ->
    Llproof.prooftree * Expr.expr list
;;
type t = {
  name : string;
  newnodes :
    Expr.expr -> int -> (Expr.expr * Expr.goalness) list -> Node.node_item list;
  make_inst : Expr.expr -> Expr.expr -> Expr.goalness -> Node.node list;
  add_formula : Expr.expr -> unit;
  remove_formula : Expr.expr -> unit;
  preprocess : Phrase.phrase list -> Phrase.phrase list;
  add_phrase : Phrase.phrase -> unit;
  postprocess : Llproof.proof -> Llproof.proof;
  to_llproof : translator;
  declare_context_coq : out_channel -> unit;
  p_rule_coq : out_channel -> Llproof.rule -> unit;
  predef : unit -> string list;
};;

let theories = ref ([] : t list);;
let active = ref ([] : t list);;

let register t = theories := t :: !theories;;

let activate name =
  try
    let t = List.find (fun t -> t.name = name) !theories in
    active := t :: !active;
  with Not_found ->
    Error.err (sprintf "no extension named %s" name);
    Error.err "The following extensions are available";
    List.iter (fun e -> Error.err e.name) !theories;
    raise Not_found;
;;

let is_active name = List.exists (fun x -> x.name = name) !active;;

let rec find_extension name l =
  match l with
  | [] -> assert false
  | h::_ when h.name = name -> h
  | _::t -> find_extension name t
;;

let get_prefix name =
  let rec spin n =
    if n >= String.length name then name
    else
      match name.[n] with
      | 'a' .. 'z' | 'A' .. 'Z' -> spin (n+1)
      | _ -> String.sub name 0 n
  in
  spin 0
;;

let newnodes e g fms =
  List.map (fun ext -> ext.newnodes e g fms) (List.rev !active)
;;

let make_inst sym m term g =
  let ext = get_prefix sym in
  if is_active ext
  then (find_extension ext !active).make_inst m term g
  else []
;;

let add_formula e =
  List.iter (fun t -> t.add_formula e) !active
;;

let remove_formula e =
  List.iter (fun t -> t.remove_formula e) !active
;;

let preprocess l =
  List.fold_left (fun hyps ext -> ext.preprocess hyps) l (List.rev !active)
;;

let add_phrase p =
  List.iter (fun ext -> ext.add_phrase p) (List.rev !active)
;;

let postprocess p =
  List.fold_left (fun prf ext -> ext.postprocess prf) p !active
;;

let to_llproof tr_expr node subs =
  match node.mlrule with
  | Ext (th, rule, args) ->
      let t = find_extension th !active in
      t.to_llproof tr_expr node subs
  | _ -> assert false
;;

let declare_context_coq oc =
  List.iter (fun ext -> ext.declare_context_coq oc) !active
;;

let p_rule_coq ext oc r =
  (find_extension ext !active).p_rule_coq oc r
;;

let predef () =
  List.flatten (["="] :: List.map (fun ext -> ext.predef ()) !active)
;;

module HE = Hashtbl.Make (Expr);;

let memorec f =
  let tbl = HE.create 997 in
  let rec ff e =
    try HE.find tbl e with
    | Not_found ->
        let res = f ff e in
        HE.add tbl e res ;
        res in
  ff
;;
