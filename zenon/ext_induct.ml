(*  Copyright 2006 INRIA  *)

(* Extension for Coq's inductive types:
   - pattern-matching
   - injectivity
   - inductive proofs
   - local fixpoint definitions
*)

open Printf;;

open Expr;;
open Misc;;
open Mlproof;;
open Node;;
open Phrase;;

exception Empty;;

type constructor_desc = {
  cd_num : int;
  cd_name : string;
  cd_type : string;
  cd_args : inductive_arg list;
};;

let constructor_table =
  (Hashtbl.create 100 : (string, constructor_desc) Hashtbl.t)
;;

let type_table =
  (Hashtbl.create 100 :
     (string, string list * (string * inductive_arg list) list * string)
     Hashtbl.t)
;;

let is_constr s = Hashtbl.mem constructor_table s;;
let constr_head e =
  match e with
  | Eapp ("@", Evar (s, _) :: _, _) when is_constr s -> true
  | Eapp (s, _, _) | Evar (s, _) when is_constr s -> true
  | _ -> false
;;

let get_constr e =
  match e with
  | Eapp ("@", Evar (s, _) :: _, _) -> s
  | Eapp (s, _, _) | Evar (s, _) -> s
  | _ -> assert false
;;

let get_args e =
  match e with
  | Eapp ("@", Evar (s, _) :: a, _) ->
     begin try
       let desc = Hashtbl.find constructor_table s in
       let (params, _, _) = Hashtbl.find type_table desc.cd_type in
       list_nth_tail a (List.length params)
     with Not_found -> assert false
     end
  | Eapp (s, a, _) -> a
  | Evar (s, _) -> []
  | _ -> assert false
;;

let rec remove_parens i j s =
  if i >= j then ""
  else if s.[i] = ' ' then remove_parens (i + 1) j s
  else if s.[j - 1] = ' ' then remove_parens i (j - 1) s
  else if s.[i] = '(' && s.[j - 1] = ')' then remove_parens (i + 1) (j - 1) s
  else String.sub s i (j - i)
;;

let remove_parens s = remove_parens 0 (String.length s) s;;

let parse_type t =
  match string_split (remove_parens t) with
  | [] -> assert false
  | c :: a -> (c, List.rev (List.map evar a))
              (* TODO check type arity vs declaration *)
;;

module HE = Hashtbl.Make (Expr);;
let tblsize = 997;;
let eqs = (HE.create tblsize : expr HE.t);;
let matches = (HE.create tblsize : ((expr -> expr) * bool * expr list) HE.t);;

let rec make_case accu e =
  match e with
  | Eapp ("$match-case", [Evar (constr, _); body], _) ->
     (constr, List.rev accu, body)
  | Elam (v, _, body, _) ->
     make_case (v :: accu) body
  | _ -> assert false
;;

let compare_cases (cs1, _, _) (cs2, _, _) =
  try
    Pervasives.compare (Hashtbl.find constructor_table cs1).cd_num
                       (Hashtbl.find constructor_table cs2).cd_num
  with Not_found -> raise Empty
;;

let normalize_cases l = List.sort compare_cases (List.map (make_case []) l);;

let make_match_redex e g ctx is_t ee cases =
  let mknode c a cases =
    let aa =
      try
        let t = Hashtbl.find constructor_table c in
        let (params, _, _) = Hashtbl.find type_table t.cd_type in
        list_nth_tail a (List.length params)
      with Not_found | Invalid_argument _ -> assert false
    in
    assert (is_constr c);
    let cs = List.map (make_case []) cases in
    let goodcase (c1, a1, b1) =
      c1 = "_" || c1 = c && List.length a1 = List.length aa
    in
    try
      let (constr, args, body) = List.find goodcase cs in
      let subs =
        if constr = "_" then []
        else List.map2 (fun v x -> (v, x)) args aa
      in
      let newbody = if subs = [] then body else substitute subs body in
      let hyp =
        if is_t then
          ctx (eapp ("Is_true", [newbody]))
        else
          ctx newbody
      in
       [ Node {
         nconc = [e];
         nrule = Ext ("induct", "match_redex", [e; hyp]);
         nprio = Arity;
         ngoal = g;
         nbranches = [| [hyp] |];
       } ]
    with Not_found | Higher_order -> []
  in
  match ee with
  | Eapp ("@", Evar (c, _) :: a, _) -> mknode c a cases
  | Eapp (c, a, _) -> mknode c a cases
  | Evar (c, _) -> mknode c [] cases
  | _ -> assert false
;;

let get_matching e =
  match e with
  | Eapp (s, [Eapp ("$match", ee :: cases, _); e2], _) when Eqrel.any s ->
     Some ((fun x -> eapp (s, [x; e2])), false, ee, cases)
  | Eapp (s, [e1; Eapp ("$match", ee :: cases, _)], _) when Eqrel.any s ->
     Some ((fun x -> eapp (s, [e1; x])), false, ee, cases)
  | Enot (Eapp (s, [Eapp ("$match", ee :: cases, _); e2], _), _)
    when Eqrel.any s ->
     Some ((fun x -> enot (eapp (s, [x; e2]))), false, ee, cases)
  | Enot (Eapp (s, [e1; Eapp ("$match", ee :: cases, _)], _), _)
    when Eqrel.any s ->
     Some ((fun x -> enot (eapp (s, [e1; x]))), false, ee, cases)
  | Eapp ("$match", ee :: cases, _) ->
     Some ((fun x -> x), false, ee, cases)
  | Enot (Eapp ("$match", ee :: cases, _), _) ->
     Some ((fun x -> enot (x)), false, ee, cases)
  (* FIXME these last 4 should only be done when ext_focal is active *)
  | Eapp ("Is_true", [Eapp ("$match", ee :: cases, _)], _) ->
     Some ((fun x -> eapp ("Is_true", [x])), false, ee, cases)
  | Eapp ("Is_true**$match", ee :: cases, _) ->
     Some ((fun x -> x), true, ee, cases)
  | Enot (Eapp ("Is_true", [Eapp ("$match", ee :: cases, _)], _), _) ->
     Some ((fun x -> enot (eapp ("Is_true", [x]))), false, ee, cases)
  | Enot (Eapp ("Is_true**$match", ee :: cases, _), _) ->
     Some ((fun x -> enot (x)), true, ee, cases)
  | _ -> None
;;

let get_unders constr =
  try
    let desc = Hashtbl.find constructor_table constr in
    let (params, _ , _) = Hashtbl.find type_table desc.cd_type in
    List.map (fun _ -> evar "_") params
  with Not_found -> assert false
;;

let make_match_branches e cases =
  match cases with
  | [] -> Error.warn "empty pattern-matching"; raise Empty
  | _ ->
      let c = normalize_cases cases in
      let f (constr, vars, body) =
        let rvars = List.map (fun _ -> Expr.newvar ()) vars in
        let pattern = eapp ("@", evar constr :: (get_unders constr) @ rvars) in
(*
        let pattern =
          match rvars with
          | [] -> evar (constr)
          | _ -> eapp (constr, rvars)
        in
*)
        let shape = enot (eapp ("=", [e; pattern])) in
        [enot (all_list rvars shape)]
      in
      List.map f c
;;

let rec get_match_case branches =
  match branches with
  | [] -> raise Not_found
  | [Eapp ("=", [_; e2], _) as shape; _] :: t when Index.member shape -> e2
  | _ :: t -> get_match_case t
;;

let get_type cases =
  match cases with
  | case :: _ ->
     let (constr, _, _) = make_case [] case in
     (Hashtbl.find constructor_table constr).cd_type
  | _ -> raise Empty
;;

let make_match_congruence e g ctx is_t ee cases rhs =
  let x = Expr.newvar () in
  (* FIXME could recover the type as in mknode below *)
  let key = if is_t then "Is_true**$match" else "$match" in
  let p = elam (x, "", ctx (eapp (key, x :: cases))) in
  Node {
    nconc = [e; eapp ("=", [ee; rhs])];
    nrule = CongruenceLR (p, ee, rhs);
    nprio = Arity;
    ngoal = g;
    nbranches = [| [apply p rhs] |];
  }
;;

let newnodes_match_cases e g =
  let mknode ctx is_t ee cases =
    let br = make_match_branches ee cases in
    let tycon = get_type cases in
    let (args, cons, schema) = Hashtbl.find type_table tycon in
    let tyargs = List.fold_left (fun s _ -> " _" ^ s) "" args in
    let x = Expr.newvar () in
    let key = if is_t then "Is_true**$match" else "$match" in
    let mctx = elam (x, sprintf "(%s%s)" tycon tyargs,
                     ctx (eapp (key, x :: cases)))
    in
    let ty = evar tycon in
    [ Node {
      nconc = [e];
      nrule = Ext ("induct", "cases", e :: ty :: mctx :: ee :: List.flatten br);
      nprio = Arity;
      ngoal = g;
      nbranches = Array.of_list br;
    }]
  in
  match get_matching e with
  | Some (ctx, is_t, ee, cases) when constr_head ee ->
     make_match_redex e g ctx is_t ee cases
  | Some (ctx, is_t, ee, cases) ->
     let l =
       List.map (make_match_congruence e g ctx is_t ee cases)
                (HE.find_all eqs ee)
     in
     if l <> [] then l else mknode ctx is_t ee cases
  | None -> []
;;

let newnodes_match_cases_eq e g =
  match e with
  | Eapp ("=", [e1; e2], _) when constr_head e2 ->
     let mknode (ctx, is_t, cases) =
       let x = Expr.newvar () in
       let key = if is_t then "Is_true**$match" else "$match" in
       let p = elam (x, "", ctx (eapp (key, x :: cases))) in
       Node {
         nconc = [apply p e1; e];
         nrule = CongruenceLR (p, e1, e2);
         nprio = Arity;
         ngoal = g;
         nbranches = [| [apply p e2] |];
       }
     in
     List.map mknode (HE.find_all matches e1)
  | _ -> []
;;

let make_induction_branch ty targs p (con, args) =
  let rec f vars args =
    match args with
    | Param s :: t ->
       let x = Expr.newvar () in
       eall (x, "", f (x :: vars) t)
    | Self :: t ->
       let x = Expr.newvar () in
       eall (x, ty, eimply (apply p x, f (x :: vars) t))
    | [] ->
       let v = eapp ("@", evar con :: List.rev vars) in
       apply p v
  in
  [enot (f targs args)]
;;

let newnodes_induction e g =
  match e with
  | Enot (Eall (_, "", _, _), _) -> []
  | Enot (Eall (v, ty, body, _), _) ->
     begin try
       let (tycon, targs) = parse_type ty in
       let (args, cons, schema) = Hashtbl.find type_table tycon in
       let p = elam (v, ty, body) in
       let br = List.map (make_induction_branch ty targs p) cons in
       [ Node {
         nconc = [e];
         nrule = Ext ("induct", "induction_notall",
                      e :: evar (tycon) :: p :: List.flatten br);
         nprio = Inst e;
         nbranches = Array.of_list br;
         ngoal = g;
       }]
     with Not_found -> []
     end
  | Eex (_, "", _, _) -> []
  | Eex (v, ty, Enot (body, _), _) ->
     begin try
       let (tycon, targs) = parse_type ty in
       let (args, cons, schema) = Hashtbl.find type_table tycon in
       let p = elam (v, ty, body) in
       let br = List.map (make_induction_branch ty targs p) cons in
       [ Node {
         nconc = [e];
         nrule = Ext ("induct", "induction_exnot",
                      e :: evar (tycon) :: p :: List.flatten br);
         nprio = Inst e;
         nbranches = Array.of_list br;
         ngoal = g;
       }]
     with Not_found -> []
     end
  | Eex (v, ty, body, _) ->
     begin try
       let (tycon, targs) = parse_type ty in
       let (args, cons, schema) = Hashtbl.find type_table tycon in
       let np = elam (v, ty, enot (body)) in
       let p = elam (v, ty, body) in
       let br = List.map (make_induction_branch ty targs np) cons in
       [ Node {
         nconc = [e];
         nrule = Ext ("induct", "induction_ex",
                      e :: evar (tycon) :: p :: List.flatten br);
         nprio = Inst e;
         nbranches = Array.of_list br;
         ngoal = g;
       }]
     with Not_found -> []
     end
  | _ -> []
;;

let rec make_lambdas args e =
  match args with
  | [] -> e
  | h :: t -> elam (h, "", make_lambdas t e)
;;

let make_case_expr constr args e =
  make_lambdas args (eapp ("$match-case", [evar (constr); e]))
;;

let newnodes_injective e g =
  let any_induct e1 e2 ty =
     let constr = get_constr e2 in
     let args = List.map (fun _ -> evar "_") (get_args e2) in
     let cas1 = make_case_expr constr args etrue in
     let cas2 = make_case_expr "_" [] efalse in
     let x = newvar () in
     let caract = elam (x, "", eapp ("$match", [x; cas1; cas2])) in
     let h = enot (eapp ("=", [e2; e1])) in
     [ Node {
      nconc = [];
       nrule = Ext ("induct", "discriminate_diff", [e2; e1; caract]);
       nprio = Arity;
       ngoal = g;
       nbranches = [| [h] |];
     } ]
  in
  match e with
  | Eapp ("=", [e1; e2], _)
    when constr_head e1 && constr_head e2 && get_constr e1 = get_constr e2 ->
     begin try
       let args1 = get_args e1 in
       let args2 = get_args e2 in
       let ty = evar ((Hashtbl.find constructor_table (get_constr e1)).cd_type)
       in
       let branch = List.map2 (fun x y -> eapp ("=", [x; y])) args1 args2 in
       [ Node {
         nconc = [e];
         nrule = Ext ("induct", "injection", [e; ty]);
         nprio = Arity;
         ngoal = g;
         nbranches = [| branch |];
       } ]
     with
     | Invalid_argument _ -> raise Empty
     | Not_found -> assert false
     end
  | Eapp ("=", [e1; e2], _) when constr_head e1 && constr_head e2 ->
     assert (get_constr e1 <> get_constr e2);
     let constr = get_constr e1 in
     let args = List.map (fun _ -> evar "_") (get_args e1) in
     let cas1 = make_case_expr constr args etrue in
     let cas2 = make_case_expr "_" [] efalse in
     let x = newvar () in
     let caract = elam (x, "", eapp ("$match", [x; cas1; cas2])) in
      [ Node {
        nconc = [e];
        nrule = Ext ("induct", "discriminate", [e; caract]);
        nprio = Arity;
        ngoal = g;
        nbranches = [| |];
      }; Stop ]
  | Enot (Eapp ("=", [e1; Eapp ("$any-induct", [Evar (ty, _); e2], _)], _), _)
    when constr_head e1 && get_constr e1 <> get_constr e2 ->
     any_induct e1 e2 ty
  | Enot (Eapp ("=", [Eapp ("$any-induct", [Evar (ty, _); e2], _); e1], _), _)
    when constr_head e1 && get_constr e1 <> get_constr e2 ->
     any_induct e1 e2 ty
  | Eapp ("=", [el; er], _) when constr_head el || constr_head er ->
     let (e1, e2) = if constr_head el then (el, er) else (er, el) in
     assert (not (constr_head e2));
     let constr = get_constr e1 in
     let desc = Hashtbl.find constructor_table constr in
     let is_multiconstr =
       try
         let (_, constrs, _) = Hashtbl.find type_table desc.cd_type in
         List.length constrs > 1
       with Not_found -> assert false
     in
     if is_multiconstr then begin
       let any = eapp ("$any-induct", [evar (desc.cd_type); e1]) in
       let h = enot (eapp ("=", [e1; any])) in
       [ Node {
         nconc = [];
         nrule = Ext ("induct", "discriminate_meta", []);
         nprio = Arity;
         ngoal = g;
         nbranches = [| [h] |];
       } ]
     end else []
  | _ -> []
;;

let constr_expr = (Hashtbl.create tblsize : (string, expr) Hashtbl.t);;

let newnodes_constr_eq e g =
  let mk_nodes e0 =
    let mk_node accu ee =
      if Expr.equal e0 ee then accu
      else begin
        let eqn = eapp ("=", [e0; ee]) in
        Node {
          nconc = [];
          nrule = Cut eqn;
          nprio = Arity;
          ngoal = g;
          nbranches = [| [eqn]; [enot eqn] |];
        } :: accu
      end
    in
    let l = Hashtbl.find_all constr_expr (get_constr e0) in
    List.fold_left mk_node [] l
  in
  let l1 =
    match e with
    | Eapp ("=", [e1; e2], _) when constr_head e1 -> mk_nodes e1
    | _ -> []
  in
  let l2 =
    match e with
    | Eapp ("=", [e1; e2], _) when constr_head e2 -> mk_nodes e2
    | _ -> []
  in
  l1 @ l2
;;


(** Match wildcard with any expression (hopefully Coq types). *)
let newnodes_wildcard e g =
  match e with
  | Enot (Eapp ("=", [Evar ("_", _); e2], _), _)
  | Enot (Eapp ("=", [e2; Evar ("_", _) ], _), _) ->
       [ Node {
         nconc = [e];
         nrule = Close_refl ("=", e2);
         nprio = Prop;
         ngoal = g;
         nbranches = [||];
       } ]
  | _ -> []
;;


let newnodes_fix e g =
  let mknode unfolded ctx fix =
    [Node {
      nconc = [e];
      nrule = Ext ("induct", "fix", [e; unfolded; ctx; fix]);
      nprio = Inst e;
      ngoal = g;
      nbranches = [| [unfolded] |];
    }; Stop]
  in
  match e with
  | Eapp ("Is_true",
          [Eapp ("$fix", (Elam (f, _, body, _) as r) :: args, _) as fix], _) ->
     begin try
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let e2 = List.fold_left apply xbody args in
       let ctx = elam (f, "", eapp ("Is_true", [f])) in
       let unfolded = apply ctx e2 in
       mknode unfolded ctx fix
     with Higher_order -> []
     end
  | Enot (Eapp ("Is_true",
                [Eapp ("$fix", (Elam (f, _, body, _) as r) :: args, _) as fix],
                _), _) ->
     begin try
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let e2 = List.fold_left apply xbody args in
       let ctx = elam (f, "", enot (eapp ("Is_true", [f]))) in
       let unfolded = apply ctx e2 in
       mknode unfolded ctx fix
     with Higher_order -> []
     end
  | Eapp (s, [Eapp ("$fix", (Elam (f, _, body, _) as r) :: args, _) as fix;
              e1], _)
    when Eqrel.any s ->
     begin try
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let e2 = List.fold_left apply xbody args in
       let ctx = elam (f, "", eapp (s, [f; e1])) in
       let unfolded = apply ctx e2 in
       mknode unfolded ctx fix
     with Higher_order -> []
     end
  | Eapp (s, [e1; Eapp ("$fix", (Elam (f, _, body, _) as r) :: args, _) as fix],
          _)
    when Eqrel.any s ->
     begin try
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let e2 = List.fold_left apply xbody args in
       let ctx = elam (f, "", eapp (s, [e1; f])) in
       let unfolded = apply ctx e2 in
       mknode unfolded ctx fix
     with Higher_order -> []
     end
  | Enot (Eapp (s, [Eapp ("$fix", (Elam (f, _, body, _) as r) :: args, _) as fix;
                    e1], _), _)
    when Eqrel.any s ->
     begin try
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let e2 = List.fold_left apply xbody args in
       let ctx = elam (f, "", enot (eapp (s, [f; e1]))) in
       let unfolded = apply ctx e2 in
       mknode unfolded ctx fix
     with Higher_order -> []
     end
  | Enot (Eapp (s, [e1;
                    Eapp ("$fix", (Elam (f, _, body, _) as r) :: args,_) as fix],
                _),_)
    when Eqrel.any s ->
     begin try
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let e2 = List.fold_left apply xbody args in
       let ctx = elam (f, "", enot (eapp (s, [e1; f]))) in
       let unfolded = apply ctx e2 in
       mknode unfolded ctx fix
     with Higher_order -> []
     end
  | _ -> []
;;

let newnodes e g _ =
    newnodes_wildcard e g
  @ newnodes_fix e g
  @ newnodes_constr_eq e g
  @ (try newnodes_match_cases e g with Empty -> [])
  @ (try newnodes_match_cases_eq e g with Empty -> [])
  @ (try newnodes_injective e g with Empty -> [])
  @ (try newnodes_induction e g with Empty -> [])
;;

let make_inst m term g = assert false;;

let rec get_decreasing_arg e env =
  match e with
  | Elam (v, t, body, _) -> get_decreasing_arg body ((v, t) :: env)
  | Eapp ("$match", v :: _, _) ->
     (try List.assoc v env
      with Not_found -> assert false)
  | _ -> assert false
;;

open Llproof;;

let to_llproof tr_expr mlp args =
  let argl = Array.to_list args in
  let hyps = List.map fst argl in
  let add = List.flatten (List.map snd argl) in
  match mlp.mlrule with
  | Ext ("induct", "injection",
         [Eapp ("=", [Eapp ("@", Evar (g, _) :: args1, _) as xx;
                      Eapp ("@", Evar (_, _) :: args2, _) as yy], _) as con;
          Evar (ty, _)]) ->
     let n_under =
       try
         let (params, _, _) = (Hashtbl.find type_table ty) in
         List.length params
       with Not_found -> assert false
     in
     let args1 = list_nth_tail args1 n_under in
     let args2 = list_nth_tail args2 n_under in
     let tc = List.map tr_expr mlp.mlconc in
     let subproof =
       match hyps with
       | [sub] -> sub
       | _ -> assert false
     in
     let rec f args1 args2 i accu =
       match args1, args2 with
       | [], [] -> accu
       | a1 :: t1, a2 :: t2 ->
          let hyp = tr_expr (eapp ("=", [a1; a2])) in
          if List.exists (Expr.equal hyp) accu.conc then begin
            let (_, cons, schema) =
              try Hashtbl.find type_table ty with Not_found -> assert false
            in
            let mk_case (name, args) =
              let params = List.map (fun _ -> Expr.newvar ()) args in
              let result = if name <> g then a1 else List.nth params i in
              let body = eapp ("$match-case", [evar (name); result]) in
              List.fold_right (fun v e -> elam (v, "", e)) params body
            in
            let cases = List.map mk_case cons in
            let x = Expr.newvar () in
            let proj = elam (x, "", eapp ("$match", x :: cases)) in
            let node = {
              conc = union tc (diff accu.conc [hyp]);
              rule = Rextension ("", "zenon_induct_f_equal",
                                 [tr_expr xx; tr_expr yy; tr_expr proj],
                                 [tr_expr con], [ [hyp] ]);
              hyps = [accu];
            } in
            f t1 t2 (i + 1) node
          end else f t1 t2 (i + 1) accu
       | _ -> assert false
     in
     (f args1 args2 0 subproof, add)
  | Ext ("induct", "injection",
         [Eapp ("=", [Eapp (g, args1, _) as xx;
                      Eapp (_, args2, _) as yy], _) as con;
          Evar (ty, _)]) ->
     let tc = List.map tr_expr mlp.mlconc in
     let subproof =
       match hyps with
       | [sub] -> sub
       | _ -> assert false
     in
     let rec f args1 args2 i accu =
       match args1, args2 with
       | [], [] -> accu
       | a1 :: t1, a2 :: t2 ->
          let hyp = tr_expr (eapp ("=", [a1; a2])) in
          if List.exists (Expr.equal hyp) accu.conc then begin
            let (_, cons, schema) =
              try Hashtbl.find type_table ty with Not_found -> assert false
            in
            let mk_case (name, args) =
              let params = List.map (fun _ -> Expr.newvar ()) args in
              let result = if name <> g then a1 else List.nth params i in
              let body = eapp ("$match-case", [evar (name); result]) in
              List.fold_right (fun v e -> elam (v, "", e)) params body
            in
            let cases = List.map mk_case cons in
            let x = Expr.newvar () in
            let proj = elam (x, "", eapp ("$match", x :: cases)) in
            let node = {
              conc = union tc (diff accu.conc [hyp]);
              rule = Rextension ("", "zenon_induct_f_equal",
                                 [tr_expr xx; tr_expr yy; tr_expr proj],
                                 [tr_expr con], [ [hyp] ]);
              hyps = [accu];
            } in
            f t1 t2 (i + 1) node
          end else f t1 t2 (i + 1) accu
       | _ -> assert false
     in
     (f args1 args2 0 subproof, add)
  | Ext ("induct", "injection", _) -> assert false
  | Ext ("induct", "discriminate", [e; car]) ->
     assert (hyps = []);
     let node = {
       conc = List.map tr_expr mlp.mlconc;
       rule = Rextension ("induct", "zenon_induct_discriminate", [],
                          [tr_expr e; tr_expr car], []);
       hyps = hyps;
     } in
     (node, add)
  | Ext ("induct", "discriminate_diff", [e1; e2; car]) ->
     let node = {
       conc = List.map tr_expr mlp.mlconc;
       rule = Rextension ("induct", "zenon_induct_discriminate_diff", [],
                          [tr_expr e1; tr_expr e2; tr_expr car], []);
       hyps = hyps;
     } in
     (node, add)
  | Ext ("induct", "match_redex", [c; h]) ->
     let tc = tr_expr c in
     let th = tr_expr h in
     let node = {
       conc = List.map tr_expr mlp.mlconc;
       rule = Rextension ("", "zenon_induct_match_redex",
                          [tc], [tc], [ [th] ]);
       hyps = hyps;
     } in
     (node, add)
  | Ext ("induct", "fix",
         [folded; unfolded; ctx;
          Eapp ("$fix", (Elam (f, _, body, _) as r)
                        :: a :: args, _)]) ->
     begin try
       let (tname, _) = parse_type (get_decreasing_arg body []) in
       let nx = Expr.newvar () in
       let foldx = elam (nx, "", eapp ("$fix", [r; nx] @ args)) in
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let unfx = elam (nx, "", List.fold_left apply xbody (nx :: args)) in
       let node = {
         conc = List.map tr_expr mlp.mlconc;
         rule = Rextension ("induct", "zenon_induct_fix",
                            List.map tr_expr [evar (tname); ctx; foldx; unfx; a],
                            [tr_expr folded],
                            [ [tr_expr unfolded] ]);
         hyps = hyps;
       } in
       (node, add)
     with Higher_order -> assert false
     end
  | Ext ("induct", "cases", c :: ty :: ctx :: m :: branches) ->
      let tc = tr_expr c in
      let tctx = tr_expr ctx in
      let tm = tr_expr m in
      let listify x = [tr_expr x] in
      let node = {
        conc = List.map tr_expr mlp.mlconc;
        rule = Rextension ("induct", "zenon_induct_cases", [ty; tctx; tm], [tc],
                           List.map listify branches);
        hyps = hyps;
      } in
      (node, add)
  | Ext ("induct", "induction_notall", c :: ty :: p :: branches) ->
     let tc = tr_expr c in
     let tp = tr_expr p in
     let listify x = [tr_expr x] in
     let node = {
       conc = List.map tr_expr mlp.mlconc;
       rule = Rextension ("induct", "zenon_induct_induction_notall",
                          [ty; tp], [tc], List.map listify branches);
       hyps = hyps;
     } in
     (node, add)
  | Ext ("induct", "induction_exnot", c :: ty :: p :: branches) ->
     let tc = tr_expr c in
     let tp = tr_expr p in
     let listify x = [tr_expr x] in
     let c0 =
       match p with
       | Elam (v, tyv, body, _) -> enot (eall (v, tyv, body))
       | _ -> assert false
     in
     let conc0 = c0 :: (Expr.diff mlp.mlconc [c]) in
     let n0 = {
       conc = List.map tr_expr conc0;
       rule = Rextension ("induct", "zenon_induct_induction_notall",
                          [ty; tp], [tr_expr c0], List.map listify branches);
       hyps = hyps;
     } in
     let n1 = {
       conc = List.map tr_expr mlp.mlconc;
       rule = Rextension ("", "zenon_induct_allexnot", [ty; tp], [tc], [[c0]]);
       hyps = [n0];
     } in
     (n1, add)
  | Ext ("induct", "induction_ex", c :: ty :: p :: branches) ->
     let tc = tr_expr c in
     let tp = tr_expr p in
     let listify x = [tr_expr x] in
     let (c0, np) =
       match p with
       | Elam (v, tyv, body, _) ->
          (enot (eall (v, tyv, enot (body))), elam (v, tyv, enot (body)))
       | _ -> assert false
     in
     let tnp = tr_expr np in
     let conc0 = c0 :: (Expr.diff mlp.mlconc [c]) in
     let n0 = {
       conc = List.map tr_expr conc0;
       rule = Rextension ("induct", "zenon_induct_induction_notall",
                          [ty; tnp], [tr_expr c0], List.map listify branches);
       hyps = hyps;
     } in
     let n1 = {
       conc = List.map tr_expr mlp.mlconc;
       rule = Rextension ("", "zenon_induct_allnotex", [ty; tp], [tc], [[c0]]);
       hyps = [n0];
     } in
     (n1, add)
  | _ -> assert false
;;

let add_induct_def ty args constrs schema =
  let f i (name, a) =
    let desc = { cd_num = i; cd_type = ty; cd_args = a; cd_name = name } in
    Hashtbl.add constructor_table name desc;
  in
  list_iteri f constrs;
  Hashtbl.add type_table ty (args, constrs, schema);
;;

let preprocess l = l;;

let add_phrase x =
  match x with
  | Hyp _ -> ()
  | Def _ -> ()
  | Sig _ -> ()
  | Inductive (ty, args, constrs, schema) ->
     add_induct_def ty args constrs schema;
;;

let postprocess l = l;;

let add_formula e =
  begin match e with
  | Eapp ("=", [e1; e2], _) when constr_head e2 ->
      HE.add eqs e1 e2;
      Hashtbl.add constr_expr (get_constr e2) e2;
  | _ -> ()
  end;
  begin match e with
  | Eapp ("=", [e1; e2], _) when constr_head e1 ->
      Hashtbl.add constr_expr (get_constr e1) e1;
  | _ -> ()
  end;
  begin match get_matching e with
  | Some (ctx, is_t, ee, cases) when not (constr_head ee) ->
      HE.add matches ee (ctx, is_t, cases)
  | _ -> ()
  end;
;;

let remove_formula e =
  begin match e with
  | Eapp ("=", [e1; e2], _) when constr_head e2 ->
      HE.remove eqs e1;
      Hashtbl.remove constr_expr (get_constr e2);
  | _ -> ()
  end;
  begin match e with
  | Eapp ("=", [e1; e2], _) when constr_head e1 ->
      Hashtbl.remove constr_expr (get_constr e1);
  | _ -> ()
  end;
  begin match get_matching e with
  | Some (ctx, is_t, ee, cases) when not (constr_head ee) ->
     HE.remove matches ee
  | _ -> ()
  end;
;;

let declare_context_coq oc =
  fprintf oc "Require Import zenon_induct.\n";
;;

let getname = Coqterm.getname;;
let p_expr = Lltocoq.p_expr;;

let rec p_list init printer sep oc l =
  match l with
  | [] -> ()
  | [x] -> fprintf oc "%s%a" init printer x;
  | h::t ->
      fprintf oc "%s%a%s" init printer h sep;
      p_list init printer sep oc t;
;;

let p_rule_coq oc r =
  let poc fmt = fprintf oc fmt in
  match r with
  | Rextension (_, "zenon_induct_discriminate", [], [conc; _], []) ->
      poc "discriminate %s.\n" (getname conc);
  | Rextension (_, "zenon_induct_discriminate_diff", [], [e1; e2; _], []) ->
      let h = enot (eapp ("=", [e1; e2])) in
      poc "assert (%a) as %s. discriminate.\n" p_expr h (getname h);
  | Rextension (_, "zenon_induct_cases", [Evar (ty, _); ctx; e1], [c], hs) ->
     poc "case_eq (%a); [\n    " p_expr e1;
     let rec get_params case =
       match case with
       | Eall (v, _, body, _) ->
          let (vs, e) = get_params body in
          let vv = Expr.newvar () in
          (vv :: vs, substitute [(v, vv)] e)
       | Enot (Eapp ("=", [_; Evar (v, _)], _), _)
       | Enot (Eapp ("=", [_; Eapp ("@", Evar (v, _) :: _, _)], _), _)
       | Enot (Eapp ("=", [_; Eapp (v, _, _)], _), _)
        -> ([], case)
       | Enot (body, _) -> get_params body
       | _ -> assert false
     in
     let params = List.map get_params (List.flatten hs) in
     let p_case oc (vs, neqn) =
       let ahyp = enot (all_list vs neqn) in
       fprintf oc "apply NNPP; zenon_intro %s\n" (getname ahyp);
     in
     fprintf oc "%a].\n" (p_list "" p_case "  | ") params;
  | Rextension (_, "zenon_induct_induction_notall", [Evar (ty, _); p], [c], hs)
    ->
     fprintf oc "apply %s.\n" (getname c);
     let (args, constrs, schema) = Hashtbl.find type_table ty in
     let unders =
       let l1 = List.map (fun _ -> "_") args in
       let l2 = List.map (fun _ -> "_") constrs in
       String.concat " " ("_" :: l1 @ l2)
     in
     fprintf oc "refine (%s %s); [" schema unders;
     let p_case oc h =
       match h with
       | [h] -> fprintf oc "apply NNPP; zenon_intro %s" (getname h);
       | _ -> assert false
     in
     p_list "" p_case " | " oc hs;
     fprintf oc "].\n";
  | Rextension (_, "zenon_induct_fix", [Evar (ty, _); ctx; foldx; unfx; a],
                [c], [ [h] ]) ->
     let (_, cstrs, schema) = Coqterm.get_induct ty in
     poc "assert (%s : %a).\n" (getname h) p_expr h;
     poc "case_eq (%a); [\n    " p_expr a;
     let p_case oc (c, args) =
       List.iter (fun _ -> fprintf oc "intro; ") args;
       fprintf oc "intro zenon_tmp; rewrite zenon_tmp in *; auto\n";
     in
     begin match a with
     | Eapp (s, _, _) | Evar (s, _) when List.mem_assoc s cstrs ->
        p_list "" p_case "  | " oc (List.filter (fun (x, _) -> x = s) cstrs);
     | _ ->
        p_list "" p_case "  | " oc cstrs;
     end;
     poc "].\n";
  | _ -> assert false
;;

let predef () = [];;

Extension.register {
  Extension.name = "induct";
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
