(*  Copyright 2005 INRIA  *)

open Printf;;

open Expr;;
open Llproof;;
open Namespace;;

module HE = Hashtbl.Make (Expr);;
let hyp_names = (HE.create 37 : string HE.t);;

let used = (Hashtbl.create 37 : (string, unit) Hashtbl.t);;

let test n = Hashtbl.mem used n;;
let add n = if not (test n) then Hashtbl.add used n ();;

let add_def p =
  match p.rule with
  | Rdefinition (_, s, _, _, _, _, _) -> add s
  | _ -> ()
;;

let add_expr e =
  try
    let name = HE.find hyp_names e in
    add name
  with Not_found -> ()
;;

let extract_name (p, dep) =
  match p with
  | Phrase.Hyp (name, e, _) -> HE.add hyp_names e name
  | _ -> ()
;;

let dowarn kind name =
  let msg = sprintf "unused %s: %s" kind name in
  Error.warn msg;
;;

let check (p, dep) =
  match p with
  | Phrase.Hyp (name, _, _) when not (test name) -> dowarn "hypothesis" name
  | Phrase.Def (DefReal (_, s, _, _, _)) when not (test s) ->
     dowarn "definition" s
  | _ -> ()
;;

let has_deps pds = List.exists snd pds;;

let warn phrases_dep p moreused =
  if !Error.warnings_flag && has_deps phrases_dep then begin
    let prf = Lazy.force p in
    Hashtbl.clear used;
    Hashtbl.add used Namespace.goal_name ();
    HE.clear hyp_names;
    List.iter extract_name phrases_dep;
    List.iter add_expr (Misc.list_last prf).proof.conc;
    Llproof.iter add_def prf;
    List.iter add moreused;
    List.iter check phrases_dep;
  end
;;


let rec check_unused name e =
  match e with
  | Evar _ | Emeta _ | Etrue | Efalse
    -> ()
  | Eapp ("$fix", Elam (f, _, body, _) :: args, _) ->
     List.iter (check_unused name) (body :: args)
  | Eapp (f, args, _) -> List.iter (check_unused name) args;
  | Enot (e1, _) -> check_unused name e1;
  | Eand (e1, e2, _) | Eor (e1, e2, _) | Eimply (e1, e2, _) | Eequiv (e1, e2, _)
    -> check_unused name e1; check_unused name e2;
  | Eall (Evar (v, _), t, e1, _) | Eex (Evar (v, _), t, e1, _)
  | Etau (Evar (v, _), t, e1, _) | Elam (Evar (v, _), t, e1, _)
    ->
       if not (Misc.is_prefix Namespace.prefix v)
          && (String.length v < 1 || v.[0] <> '_')
          && not (List.mem v (get_fv e1))
       then begin
         Error.warn (sprintf "unused variable (%s : %s) in %s" v t name);
       end;
       check_unused name e1;
  | Eall _ | Eex _ | Etau _ | Elam _ -> assert false
;;

let warn_unused_var phr_dep =
  let f (p, _) =
    match p with
    | Phrase.Hyp (name, e, _) -> check_unused name e
    | Phrase.Def (DefReal (_, name, _, body, _)) -> check_unused name body
    | Phrase.Def (DefRec (_, name, _, body)) -> check_unused name body
    | Phrase.Def (DefPseudo _) -> assert false
    | Phrase.Sig _ -> ()
    | Phrase.Inductive _ -> ()
  in
  List.iter f phr_dep
;;
