(*  Copyright 2002 INRIA  *)

open Expr;;
open Misc;;
open Mlproof;;
open Node;;
open Printf;;

let ( =%= ) = ( = );;
let ( = ) = Expr.equal;;

type state = {
  queue : queue;
  (* forms : indexes of the current branch's formulas *)
  (* cur_depth : int; *)
  (* extended_state : state records of the active extensions *)
};;

type branch_state =
  | Open
  | Closed of proof
  | Backtrack
;;

type frame = {
  node : node;
  state : state;
  brst : branch_state array;
  curbr : int;
};;

(***************)

let cur_depth = ref 0;;
let top_depth = ref 0;;
let max_depth = ref 1_000_000_000;;

let steps = ref 0.;;

(****************)

let complement fm =
  match fm with
  | Enot (p, _) -> (p, p)
  | p -> (enot (p), p)
;;

let rec replace_meta m va e =
  match e with
  | Evar _ -> e
  | Emeta _ -> if Expr.equal e m then va else e
  | Eapp (s, args, _) -> eapp (s, List.map (replace_meta m va) args)
  | Enot (f, _) -> enot (replace_meta m va f)
  | Eand (f, g, _) -> eand (replace_meta m va f, replace_meta m va g)
  | Eor (f, g, _) -> eor (replace_meta m va f, replace_meta m va g)
  | Eimply (f, g, _) -> eimply (replace_meta m va f, replace_meta m va g)
  | Eequiv (f, g, _) -> eequiv (replace_meta m va f, replace_meta m va g)
  | Etrue -> e
  | Efalse -> e
  | Eall (v, t, f, _) -> eall (v, t, replace_meta m va f)
  | Eex (v, t, f, _) -> eex (v, t, replace_meta m va f)
  | Etau (v, t, f, _) -> etau (v, t, replace_meta m va f)
  | Elam (v, t, f, _) -> elam (v, t, replace_meta m va f)
;;

let is_meta = function
  | Emeta _ -> true
  | _ -> false
;;

let rec pure_meta l =
  let rec all_different l =
    match l with
    | [] -> true
    | h::t -> not (List.exists (Expr.equal h) t)
              && all_different t
  in
  match l with
  | [] -> false
  | [Eapp (_, l1, _)] -> pure_meta l1
  | _ -> List.for_all is_meta l && all_different l
;;

(****************)

let add_node st n =
  { (*st with*) queue = insert st.queue n }
;;

let add_node_list st ns =
  List.fold_left add_node st ns
;;

let make_inst st m term g =
  match m with
  | Eall (v, t, p, _) ->
      let n = Expr.substitute [(v, term)] p in
      add_node st {
        nconc = [m];
        nrule = All (m, term);
        nprio = Inst m;
        ngoal = g;
        nbranches = [| [n] |];
      }, false
  | Eex (v, t, p, _) ->
      let n = Expr.substitute [(v, term)] (enot p) in
      let nm = enot (m) in
      add_node st {
        nconc = [nm];
        nrule = NotEx (nm, term);
        nprio = Inst m;
        ngoal = g;
        nbranches = [| [n] |];
      }, false
  | Eapp (sym, _, _) ->
     add_node_list st (Extension.make_inst sym m term g), false
  | _ -> assert false
;;

(* [make_inequals l1 l2]
   l1 and l2 are the same length
   returns the pairwise inequalities between corresponding elements of l1 and l2
   return it as a list of lists
*)
let rec make_inequals_aux l1 l2 =
  match l1, l2 with
  | [], [] -> []
  | h1::t1, h2::t2 ->
      [enot (eapp ("=", [h1; h2]))] :: make_inequals_aux t1 t2
  | _, _ -> assert false
;;
let make_inequals l1 l2 = Array.of_list (make_inequals_aux l1 l2);;

let arity_warning s =
  match s with
  | "TLA.set" | "TLA.tuple" | "TLA.record" | "TLA.recordset" -> ()
  | "@" | "$match" -> ()
  | _ ->
     Error.warn (sprintf "symbol %s is used with inconsistent arities" s);
;;

let higher_order_warning s =
  Error.warn (sprintf "symbol %s is used in higher-order substitution" s);
;;

let rec good_match_e e1 e2 =
  match e1, e2 with
  | Evar (v1, _), Evar (v2, _) -> v1 =%= v2
  | Emeta _, _ -> true
  | _, Emeta _ -> true
  | Eapp (s1, args1, _), Eapp (s2, args2, _) -> s1 =%= s2
  | Enot (e1, _), Enot (e2, _) -> good_match_e e1 e2
  | Eand (e1, e2, _), Eand (e3, e4, _)
  | Eor (e1, e2, _), Eor (e3, e4, _)
  | Eimply (e1, e2, _), Eimply (e3, e4, _)
  | Eequiv (e1, e2, _), Eequiv (e3, e4, _)
  -> good_match_e e1 e3 || good_match_e e2 e4
  | Etrue, Etrue -> true
  | Efalse, Efalse -> true
  | Eall _, _ | Eex _, _ | Elam _, _ -> false
  | Etau _, Etau _ -> Expr.equal e1 e2
  | _ -> false
;;

let good_match l1 l2 =
  match l1, l2 with
  | [], [] -> true
  | _ -> List.for_all2 good_match_e l1 l2
;;

let rec constructor_mismatch e1 e2 =
  let isc = Ext_induct.is_constr in
  match e1, e2 with
  | Evar (v1, _), Evar (v2, _) when v1 <> v2 && isc v1 && isc v2 -> true
  | Eapp (s1, _, _), Eapp (s2, _, _) when s1 <> s2 && isc s1 && isc s2 -> true
  | Eapp (s1, args1, _), Eapp (s2, args2, _) when s1 =%= s2 && isc s1 ->
     begin try List.exists2 constructor_mismatch args1 args2
     with Invalid_argument _ -> false
     end
  | _, _ -> false
;;

let make_notequiv st sym (p, g) (np, ng) =
  match p, np with
  | Eapp ("TLA.in", [e1; Evar _ as s1], _),
      Enot (Eapp (_, [e2; s2], _), _)
    when not (Expr.equal s1 s2)
         && not (is_meta e1 || is_meta s1 || is_meta e2 || is_meta s2)
         && not (Expr.equal e1 e2)
    -> st
  | Eapp ("Is_true", _, _), _ when Extension.is_active "focal" -> st
  | Eapp (s1, args1, _), Enot (Eapp (s2, args2, _), _) ->
      assert (s1 =%= s2);
      if sym && List.length args2 != 2
         || List.length args1 <> List.length args2
      then (arity_warning s1; st)
      else if Extension.is_active "induct"
              && List.exists2 constructor_mismatch args1 args2 then st
      else begin
        let myrule = if sym then P_NotP_sym (s1, p, np) else P_NotP (p, np) in
        let myargs1 = if sym then List.rev args1 else args1 in
        let prio =
          if good_match args1 args2 then
            if s1 =%= "=" then Arity_eq else Arity
          else Inst p
        in
        add_node st {
          nconc = [p; np];
          nrule = myrule;
          nprio = prio;
          ngoal = min g ng;
          nbranches = make_inequals myargs1 args2;
        }
      end
  | _ -> assert false
;;

(* [is_conj f m]:
   f is a n-ary conjunctive formula
   return 0 if n >= m; return m-n otherwise
*)
let rec is_conj f m =
  if m <= 0 then 0 else
  match f with
  | Eand (a, b, _) -> is_conj b (is_conj a m)
  | Enot (a, _) -> is_disj a m
  | _ -> m-1

and is_disj f m =
  if m <= 0 then 0 else
  match f with
  | Eor (a, b, _) -> is_disj b (is_disj a m)
  | Eimply (a, b, _) -> is_disj b (is_conj a m)
  | Enot (a, _) -> is_conj a m
  | _ -> m-1
;;

let rec decomp_conj neg accu f =
  match f with
  | Eand (a, b, _) -> decomp_conj neg (decomp_conj neg accu b) a
  | Enot (a, _) -> decomp_disj (not neg) accu a
  | _ when neg -> enot (f) :: accu
  | _ -> f :: accu

and decomp_disj neg accu f =
  match f with
  | Eor (a, b, _) -> decomp_disj neg (decomp_disj neg accu b) a
  | Eimply (a, b, _) -> decomp_conj (not neg) (decomp_disj neg accu b) a
  | Enot (a, _) -> decomp_conj (not neg) accu a
  | _ when neg -> enot (f) :: accu
  | _ -> f :: accu
;;

let newnodes_absurd st fm g _ =
  match fm with
  | Enot (p, _) when Index.member p -> add_node st {
      nconc = [fm; p];
      nrule = Close (p);
      nprio = Prop;
      ngoal = g;
      nbranches = [| |];
    }, true
  | p when Index.member (enot p) -> add_node st {
      nconc = [p; enot p];
      nrule = Close (p);
      nprio = Prop;
      ngoal = g;
      nbranches = [| |];
    }, true
  | _ -> st, false
;;

let newnodes_closure st fm g _ =
  match fm with
  | Efalse -> add_node st {
      nconc = [fm];
      nrule = False;
      nprio = Prop;
      ngoal = g;
      nbranches = [| |];
    }, true
  | Enot (Etrue, _) -> add_node st {
      nconc = [fm];
      nrule = NotTrue;
      nprio = Prop;
      ngoal = g;
      nbranches = [| |];
    }, true
  | Enot (Eapp (s, [a; b], _), _) when Eqrel.refl s && Expr.equal a b ->
    add_node st {
      nconc = [fm];
      nrule = Close_refl (s, a);
      nprio = Prop;
      ngoal = g;
      nbranches = [| |];
    }, true
  | Eapp (s, [e1; e2], _)
    when Eqrel.sym s && Index.member (enot (eapp (s, [e2; e1]))) ->
    add_node st {
      nconc = [fm; (enot (eapp (s, [e2; e1])))];
      nrule = Close_sym (s, e1, e2);
      nprio = Prop;
      ngoal = g;
      nbranches = [| |];
    }, true
  | Enot (Eapp (s, [e1; e2], _), _)
    when Eqrel.sym s && Index.member (eapp (s, [e2; e1])) ->
    add_node st {
      nconc = [fm; (eapp (s, [e2; e1]))];
      nrule = Close_sym (s, e2, e1);
      nprio = Prop;
      ngoal = g;
      nbranches = [| |];
    }, true
  | Eapp ("=", [Eapp ("$string", [v1], _);
                Eapp ("$string", [v2], _)], _) when not (Expr.equal v1 v2) ->
     add_node st {
       nconc = [fm];
       nrule = Ext ("", "stringequal", [v1; v2]);
       nprio = Prop;
       ngoal = g;
       nbranches = [| |];
     }, true
  | _ -> st, false
;;

let newnodes_eq_str st fm g _ =
  let mk_node (st, b) rule e1 s1 e2 s2 eq =
    if Expr.equal s1 s2 then (st, b) else
    add_node st {
      nconc = [fm; eq];
      nrule = Ext ("", rule, [e1; s1; e2; s2]);
      nprio = Prop;
      ngoal = g;
      nbranches = [| [enot (eapp ("=", [e1; e2]))] |];
    }, false
  in
  match fm with
  | Eapp ("=", [e1; Eapp ("$string", [_], _) as s1], _) ->
     let l = Index.find_eq_str () in
     let r = Index.find_str_eq () in
     let fl st (e2, s) =
       let s2 = eapp ("$string", [evar s]) in
       let eq = eapp ("=", [e2; s2]) in
       mk_node st "stringdiffll" e1 s1 e2 s2 eq
     in
     let fr st (e2, s) =
       let s2 = eapp ("$string", [evar s]) in
       let eq = eapp ("=", [s2; e2]) in
       mk_node st "stringdifflr" e1 s1 e2 s2 eq
     in
     List.fold_left fr (List.fold_left fl (st, false) l) r
  | Eapp ("=", [Eapp ("$string", [_], _) as s1; e1], _) ->
     let l = Index.find_eq_str () in
     let r = Index.find_str_eq () in
     let fl st (e2, s) =
       let s2 = eapp ("$string", [evar s]) in
       let eq = eapp ("=", [e2; s2]) in
       mk_node st "stringdiffrl" e1 s1 e2 s2 eq
     in
     let fr st (e2, s) =
       let s2 = eapp ("$string", [evar s]) in
       let eq = eapp ("=", [s2; e2]) in
       mk_node st "stringdiffrr" e1 s1 e2 s2 eq
     in
     List.fold_left fr (List.fold_left fl (st, false) l) r
  | _ -> st, false
;;

let newnodes_jtree st fm g _ =
  match fm with
  | Eand _ | Enot (Eor _, _) | Enot (Eimply _, _)
    when is_conj fm 3 == 0 ->
      add_node st {
        nconc = [fm];
        nrule = ConjTree fm;
        nprio = Prop;
        ngoal = g;
        nbranches = [| decomp_conj false [] fm |];
      }, true
  | Eor _ | Enot (Eand _, _) | Eimply _
    when is_disj fm 3 == 0 ->
      let forms = Array.of_list (decomp_disj false [] fm) in
      let branches = Array.map (fun x -> [x]) forms in
      add_node st {
        nconc = [fm];
        nrule = DisjTree fm;
        nprio = Prop;
        ngoal = g;
        nbranches = branches;
      }, true
  | _ -> st, false
;;

let newnodes_alpha st fm g _ =
  match fm with
  | Enot (Enot (a, _), _) ->
      add_node st {
        nconc = [fm];
        nrule = NotNot (a);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [a] |];
      }, true
  | Eand (a, b, _) ->
      add_node st {
        nconc = [fm];
        nrule = And (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [a; b] |];
      }, true
  | Enot (Eor (a, b, _), _) ->
      add_node st {
        nconc = [fm];
        nrule = NotOr (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [enot (a); enot (b)] |];
      }, true
  | Enot (Eimply (a, b, _), _) ->
      add_node st {
        nconc = [fm];
        nrule = NotImpl (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [a; enot (b)] |];
      }, true
  | _ -> st, false
;;

let newnodes_beta st fm g _ =
  match fm with
  | Eor (a, b, _) ->
      add_node st {
        nconc = [fm];
        nrule = Or (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [a]; [b] |];
      }, true
  | Eimply (a, b, _) ->
      add_node st {
        nconc = [fm];
        nrule = Impl (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [enot (a)]; [b] |];
      }, true
  | Enot (Eand (a, b, _), _) ->
      add_node st {
        nconc = [fm];
        nrule = NotAnd (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [enot (a)]; [enot (b)] |];
      }, true
  | Eequiv (a, b, _) ->
      add_node st {
        nconc = [fm];
        nrule = Equiv (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [enot (a); enot (b)]; [a; b] |];
      }, true
  | Enot (Eequiv (a, b, _), _) ->
      add_node st {
        nconc = [fm];
        nrule = NotEquiv (a, b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [enot (a); b]; [a; enot (b)] |];
      }, true
  | _ -> st, false
;;

let get_var_name e =
  match e with
  | Evar (name, _) -> name
  | _ -> assert false
;;

let orelse f1 x1 f2 x2 =
  match f1 x1 with
  | None -> f2 x2
  | x -> x
;;

let andalso f1 x1 f2 x2 =
  match f1 x1 with
  | None -> None
  | Some r1 ->
     match f2 x2 with
     | None -> None
     | Some r2 -> Some (Expr.union r1 r2)
;;

let interferes env vs =
  let p ee =
    let fv = get_fv ee in
    List.exists (fun x -> List.mem x fv) env
  in
  List.exists p vs
;;

let has_free_var v e = List.mem v (get_fv e);;

let newnodes_delta st fm g _ =
  match fm with
  | Eex (v, t, p, _) ->
     let h = substitute [(v, etau (v, t, p))] p in
     add_node st {
       nconc = [fm];
       nrule = Ex (fm);
       nprio = Prop;
       ngoal = g;
       nbranches = [| [h] |];
     }, true
  | Enot (Eall (v, t, p, _), _) ->
     let h1 = substitute [(v, etau (v, t, enot p))] (enot p) in
     let h2 = eex (v, t, enot p) in
     add_node st {
       nconc = [fm];
       nrule = NotAllEx (fm);
       nprio = Prop;
       ngoal = g;
       nbranches = [| [h1; h2] |];
     }, true
  | _ -> st, false
;;

let newnodes_gamma st fm g _ =
  match fm with
  | Eall (v, t, p, _) ->
      let w = emeta (fm) in
      let branches = [| [Expr.substitute [(v, w)] p] |] in
      add_node st {
        nconc = [fm];
        nrule = All (fm, w);
        nprio = Arity;
        ngoal = g;
        nbranches = branches;
      }, true
  | Enot (Eex (v, t, p, _) as fm1, _) ->
      let w = emeta (fm1) in
      let branches = [| [enot (Expr.substitute [(v, w)] p)] |] in
      add_node st {
        nconc = [fm];
        nrule = NotEx (fm, w);
        nprio = Arity;
        ngoal = g;
        nbranches = branches;
      }, true
  | _ -> st, false
;;

let newnodes_unfold st fm g _ =
  let mk_unfold ctx p args =
    try
      let (d, params, body) = Index.get_def p in
      let prio =
        match d with
        | DefRec _ | DefReal (_, _, _, _, Some _) -> Inst fm
        | _ -> Prop
      in
      match params, args, body with
      | [], Some aa, Evar (b, _) ->
         let unfolded = ctx (eapp (b, aa)) in
         add_node st {
           nconc = [fm];
           nrule = Definition (d, fm, unfolded);
           nprio = prio;
           ngoal = g;
           nbranches = [| [unfolded] |];
         }, true
      | _ ->
         let aa = match args with None -> [] | Some l -> l in
         let subst = List.map2 (fun x y -> (x,y)) params aa in
         let unfolded = ctx (substitute_2nd subst body) in
         add_node st {
           nconc = [fm];
           nrule = Definition (d, fm, unfolded);
           nprio = prio;
           ngoal = g;
           nbranches = [| [unfolded] |];
         }, true
    with
    | Higher_order -> higher_order_warning p; (st, false)
    | Invalid_argument _ -> arity_warning p; (st, false)
    | Not_found -> assert false
  in
  match fm with
  | Eapp (p, args, _) when Index.has_def p ->
     let ctx x = x in
     mk_unfold ctx p (Some args)
  | Enot (Eapp (p, args, _), _) when Index.has_def p ->
     let ctx x = enot (x) in
     mk_unfold ctx p (Some args)
  | Eapp (s, [Eapp (p, args, _); e], _) when Eqrel.any s && Index.has_def p ->
     let ctx x = eapp (s, [x; e]) in
     mk_unfold ctx p (Some args)
  | Eapp (s, [e; Eapp (p, args, _)], _) when Eqrel.any s && Index.has_def p ->
     let ctx x = eapp (s, [e; x]) in
     mk_unfold ctx p (Some args)
  | Enot (Eapp (s, [Eapp (p, args, _); e], _), _)
    when Eqrel.any s && Index.has_def p ->
     let ctx x = enot (eapp (s, [x; e])) in
     mk_unfold ctx p (Some args)
  | Enot (Eapp (s, [e; Eapp (p, args, _)], _), _)
    when Eqrel.any s && Index.has_def p ->
     let ctx x = enot (eapp (s, [e; x])) in
     mk_unfold ctx p (Some args)
  | Evar (v, _) when Index.has_def v ->
     let ctx x = x in
     mk_unfold ctx v None
  | Enot (Evar (v, _), _) when Index.has_def v ->
     let ctx x = enot (x) in
     mk_unfold ctx v None
  | Eapp (s, [Evar (v, _); e], _) when Eqrel.any s && Index.has_def v ->
     let ctx x = eapp (s, [x; e]) in
     mk_unfold ctx v None
  | Eapp (s, [e; Evar (v, _)], _) when Eqrel.any s && Index.has_def v ->
     let ctx x = eapp (s, [e; x]) in
     mk_unfold ctx v None
  | Enot (Eapp (s, [Evar (v, _); e], _), _)
    when Eqrel.any s && Index.has_def v ->
     let ctx x = enot (eapp (s, [x; e])) in
     mk_unfold ctx v None
  | Enot (Eapp (s, [e; Evar (v, _)], _), _)
    when Eqrel.any s && Index.has_def v ->
     let ctx x = enot (eapp (s, [e; x])) in
     mk_unfold ctx v None
  | _ -> st, false
;;

let orient_meta m1 m2 =
  let rec get_metas e =
    match e with
    | Evar _ -> []
    | Emeta (m, _) -> m :: get_metas m
    | Eapp (s, es, _) -> List.fold_left (fun a e -> get_metas e @@ a) [] es
    | Enot (e1, _) -> get_metas e1
    | Eand (e1, e2, _) | Eor (e1, e2, _) | Eimply (e1, e2, _)
    | Eequiv (e1, e2, _)
      -> get_metas e1 @@ get_metas e2
    | Etrue | Efalse -> []
    | Eall (v, t, e1, _) | Eex (v, t, e1, _) | Etau (v, t, e1, _)
    | Elam (v, t, e1, _)
      -> get_metas e1
  in
  let l1 = get_metas m1 in
  let l2 = get_metas m2 in
  if List.memq m1 l2 then false
  else if List.memq m2 l1 then true
  else List.length l1 > List.length l2
;;

let newnodes_refl st fm g _ =
  match fm with
  | Enot (Eapp (s, [e1; e2], _), _) when s <> "=" && Eqrel.refl s ->
      add_node st {
        nconc = [fm];
        nrule = Refl (s, e1, e2);
        nprio = Arity;
        ngoal = g;
        nbranches = [| [enot (eapp ("=", [e1; e2]))] |];
      }, false

  | Enot (Eapp ("=", [Emeta (m1, _) as e1; Emeta (m2, _) as e2], _), _) ->
     let (st1, _) = make_inst st m2 e1 g in
     make_inst st1 m1 e2 g
  | Enot (Eapp ("=", [Emeta (m, _); e], _), _) -> make_inst st m e g
  | Enot (Eapp ("=", [e; Emeta (m, _)], _), _) -> make_inst st m e g

  | _ -> st, false
;;

let newnodes_match_congruence st fm g _ =
  match fm with
  | Enot (Eapp ("=", [Eapp ("$string", [s1], _);
                      Eapp ("$string", [s2], _)], _), _)
    when not (Expr.equal s1 s2) ->
     (st, false)
  | Enot (Eapp ("=", [(Eapp (f1, a1, _) as e1);
                      (Eapp (f2, a2, _) as e2)], _), _)
    when f1 =%= f2 ->
      if List.length a1 == List.length a2 then begin
        add_node st {
          nconc = [fm];
          nrule = NotEqual (e1, e2);
          nprio = Arity;
          ngoal = g;
          nbranches = make_inequals a1 a2;
        }, false
      end else (arity_warning f1; (st, false))
(*
  FIXME determiner si c'est utile...
  | Enot (Eapp ("=", [Etau (v1, t1, f1, _); Etau (v2, t2, f2, _)], _), _) ->
      let f2a = Expr.substitute [(v2, v1)] f2 in
      let u = Expr.preunify f1 f2a in
      let f (st, _) (m, e) = make_inst st m e in
      List.fold_left f (st, false) u
*)
  | _ -> st, false
;;

let mknode_trans sym (e1, g1) (e2, g2) =
  let (r, a, b, c, d) =
    match e1, e2 with
    | Eapp (r, [a; b], _), Enot (Eapp (rr, [c; d], _), _) ->
      assert (r =%= rr);
      (r, a, b, c, d)
    | _, _ -> assert false
  in
  let (x, y, z, t) = if sym then (d, a, b, c) else (c, a, b, d) in
  let branches = [|
    [enot (eapp ("=", [x; y])); enot (eapp (r, [x; y]))];
    [enot (eapp ("=", [z; t])); enot (eapp (r, [z; t]))];
  |] in
  {
    nconc = [e1; e2];
    nrule = if sym then Trans_sym (e1, e2) else Trans (e1, e2);
    nprio = if r =%= "=" then Arity_eq else Arity;
    ngoal = min g1 g2;
    nbranches = branches;
  }
;;

let mknode_negtrans sym eg2 eg1 = mknode_trans sym eg1 eg2;;

let mknode_transeq sym (e1, g1) (e2, g2) =
  let (r, a, b, c, d) =
    match e1, e2 with
    | Eapp ("=", [a; b], _), Enot (Eapp (r, [c; d], _), _) -> (r, a, b, c, d)
    | _, _ -> assert false
  in
  let rsym = Eqrel.sym r in
  let (x, y, z, t) =
    if sym then
      if rsym then (d, a, b, c) else (c, b, a, d)
    else (c, a, b, d)
  in
  let branches = [|
    [enot (eapp ("=", [x; y])); enot (eapp (r, [x; y]))];
    [enot (eapp (r, [x; y])); enot (eapp (r, [z; t]))];
    [enot (eapp ("=", [z; t])); enot (eapp (r, [z; t]))];
  |] in
  {
    nconc = [e1; e2];
    nrule =
      if sym then
        if rsym then TransEq_sym (a, b, e2) else TransEq2 (a, b, e2)
      else TransEq (a, b, e2);
    nprio = if r =%= "=" then Arity_eq else Arity;
    ngoal = min g1 g2;
    nbranches = branches;
  }
;;

let mknode_negtranseq sym eg2 eg1 = mknode_transeq sym eg1 eg2;;

let get_rhs (e, g) =
  match e with
  | Eapp (_, [f1; f2], _) -> (f2, g)
  | _ -> assert false
;;

let get_lhs (e, g) =
  match e with
  | Eapp (_, [f1; f2], _) -> (f1, g)
  | _ -> assert false
;;

let preunif_g e1 (e2, g2) =
  List.map (fun (m, e) -> (m, e, g2)) (preunify e1 e2)
;;

let newnodes_match_trans st fm g _ =
  try
    let fmg = (fm, g) in
    match fm with
    | Eapp ("=", [Emeta (m1, _); Emeta (m2, _)], _) ->
       let nodes = List.map (mknode_transeq false fmg) (Index.find_neg "=") in
       add_node_list st nodes, false
    | Eapp ("=", [e1; e2], _) ->
        Index.add_trans fm;
        let h1 = Index.get_head e1 in
        let h2 = Index.get_head e2 in
        let matches_ll = Index.find_all_negtrans_left h1 in
        let matches_rr = Index.find_all_negtrans_right h2 in
        let matches_lr = Index.find_all_negtrans_left h2 in
        let matches_rl = Index.find_all_negtrans_right h1 in
        let nodes = List.flatten [
          List.map (mknode_transeq false fmg) matches_ll;
          List.map (mknode_transeq true fmg) matches_lr;
          List.map (mknode_transeq true fmg) matches_rl;
          List.map (mknode_transeq false fmg) matches_rr;
        ] in
        add_node_list st nodes, false
    | Eapp (s, [e1; e2], _) when Eqrel.trans s ->
        Index.add_trans fm;
        let h1 = Index.get_head e1 in
        let h2 = Index.get_head e2 in
        let matches_ll = Index.find_negtrans_left s h1 in
        let matches_rr = Index.find_negtrans_right s h2 in
        let matches_lr =
          if Eqrel.sym s then Index.find_negtrans_left s h2 else []
        in
        let matches_rl =
          if Eqrel.sym s then Index.find_negtrans_right s h1 else []
        in
        let nodes = List.flatten [
          List.map (mknode_trans false fmg) matches_ll;
          List.map (mknode_trans true fmg) matches_lr;
          List.map (mknode_trans true fmg) matches_rl;
          List.map (mknode_trans false fmg) matches_rr;
        ] in
        add_node_list st nodes, false
    | Enot (Eapp (s, [e1; e2], _), _) when Eqrel.trans s ->
        Index.add_negtrans fm;
        let h1 = Index.get_head e1 in
        let h2 = Index.get_head e2 in
        let matches_ll = Index.find_trans_left s h1 in
        let matches_rr = Index.find_trans_right s h2 in
        let matches_lr =
          if Eqrel.sym s then Index.find_trans_right s h1 else []
        in
        let matches_rl =
          if Eqrel.sym s then Index.find_trans_left s h2 else []
        in
        let nodes = List.flatten [
          List.map (mknode_negtrans false fmg) matches_ll;
          List.map (mknode_negtrans true fmg) matches_lr;
          List.map (mknode_negtrans true fmg) matches_rl;
          List.map (mknode_negtrans false fmg) matches_rr;
        ] in
        let eqnodes =
          if s =%= "=" then [] else
          let eqmatches_ll = Index.find_trans_left "=" h1 in
          let eqmatches_rr = Index.find_trans_right "=" h2 in
          let eqmatches_lr = Index.find_trans_right "=" h1 in
          let eqmatches_rl = Index.find_trans_left "=" h2 in
          List.flatten [
            List.map (mknode_negtranseq false fmg) eqmatches_ll;
            List.map (mknode_negtranseq true fmg) eqmatches_lr;
            List.map (mknode_negtranseq true fmg) eqmatches_rl;
            List.map (mknode_negtranseq false fmg) eqmatches_rr;
          ]
        in
        add_node_list st (eqnodes @@ nodes), false
    | _ -> st, false
  with Index.No_head -> st, false
;;

let newnodes_match_sym st fm g _ =
  let fmg = (fm, g) in
  match fm with
  | Enot (Eapp (s, [a1; a2], _), _) when s <> "=" && Eqrel.sym s ->
      let do_match st pg = make_notequiv st true pg fmg in
      List.fold_left do_match st (Index.find_pos s), false
  | Eapp (s, [a1; a2], _) when s <> "=" && Eqrel.sym s ->
      let do_match st pg = make_notequiv st true fmg pg in
      List.fold_left do_match st (Index.find_neg s), false
  | _ -> (st, false)
;;

let newnodes_match st fm g _ =
  let fmg = (fm, g) in
  match fm with
  | Enot (Eapp (s, _, _), _) when s <> "=" ->
      let do_match st pg = make_notequiv st false pg fmg in
      List.fold_left do_match st (Index.find_pos s), true
  | Eapp (s, _, _) when s <> "=" ->
      let do_match st pg = make_notequiv st false fmg pg in
      List.fold_left do_match st (Index.find_neg s), true
  | _ -> (st, false)
;;

(*  goodmatch stuff, not ready yet

type match_type =
  | Nimply
  | Nequiv
  | Nequal
  | Nsubset
  | Nle
  | Nlt
;;

exception Mismatch;;

(* env: list of (left-var, right-var, inst-left-p)
   mt: match_type
   e1: left-e
   e2: right-e
   lr: bool (left-to-right)
*)

let rec get_match env mt e1 e2 lr =
  match mt, e1, e2, lr with
  | Nlt, Evar (s1, _), e2, true when is_bound s1 env true -> raise Mismatch
  | Nlt, e1, Evar (s2, _), false when is_bound s2 env false -> raise Mismatch
  | _, Evar (s1, _), e2, true when check_env s1 e2 env true -> ([(s1, e2)], [])
  | _, e1, Evar (s2, _), false when check_env s2 e1 env false -> ([(s2, e1)], [])
  | Nlt, e1, e2, _ when Expr.equal e1 e2 -> raise Mismatch
  | _, e1, e2 when Expr.equal e1 e2 -> ([], [])
  | Nimply, Enot (e1, _), Enot (e2, _), _ -> get_match env Nimply e1 e2 (not lr)
  | Nimply, Eand (e1a, e1b, _), Eand (e2a, e2b), _ ->
     let insta, nodesa = get_match env Nimply e1a e2a lr in
     let instb, nodesb = get_match env Nimply e1b e2b lr in
     (merge_inst insta instb, nodesa @ nodesb)
  | Nimply, Eor (e1a, e1b, _), Eor (e2a, e2b), _ ->
     let insta, nodesa = get_match env Nimply e1a e2a lr in
     let instb, nodesb = get_match env Nimply e1b e2b lr in
     (merge_inst insta instb, nodesa @ nodesb)
  | Nimply, Eimply (e1a, e1b, _), Eimply (e2a, e2b), _ ->
     let insta, nodesa = get_match env Nimply e1a e2a (not lr) in
     let instb, nodesb = get_match env Nimply e1b e2b lr in
     (merge_inst insta instb, nodesa @ nodesb)
  | Nimply, Eequiv (e1a, e1b, _), Eequiv (e2a, e2b), _ ->
     let insta, nodesa = get_match env Nequiv e1a e2a true in
     let instb, nodesb = get_match env Nequiv e1b e2b true in
     (merge_inst insta instb, nodesa @ nodesb)
  | Nimply, Efalse, _, true -> ([], [])
  | Nimply, _, Efalse, false -> ([], [])
  | Nimply, _, Etrue, true -> ([], [])
  | Nimply, Etrue, _, false -> ([], [])
  | Nimply, Eall (x1, t1, b1, _), Eall (x2, t2, b2, _), _ ->
     let newenv = (x1, x2, lr) :: env in
     let inst, nodes = get_match newenv Nimply b1 b2 lr in
     (erase_inst x1 x2 lr inst, nodes)
  | Nimply, Eex (x1, t1, b1, _), Eex (x2, t2, b2, _), _ ->
     let newenv = (x1, x2, not lr) :: env in
     let inst, nodes = get_match newenv Nimply b1 b2 (not lr) in
     (erase_inst x1 x2 (not lr) inst, nodes
  | Nimply, Eapp ("=", [e1a; e1b], _), Eapp ("=", [e2a; e2b], _), _ ->
     let insta, nodesa = get_match env Nequal e1a e2a true in
     let instb, nodesb = get_match env Nequal e1b e2b true in
     (merge_inst insta instb, nodesa @ nodesb)
  | Nimply, Eapp ("arith.le", [e1a; e1b], _), Eapp ("arith.le", [e1a; e1b], _),
    _ ->
     let insta, nodesa = get_match env Nle e2a e1a true in
     let instb, nodesb = get_match env Nequal e1b e2b true in
     ...
;;

let mk_goodmatch e1 ne2 =
  let e2 = match ne2 with Enot (e2, _) -> e2 | _ -> assert false in
  let (nsym, branches) = get_match [Nimply (e1, e2)] [] (0, []) in
  if nsym > !Globals.good_match_size
  then
    [ Node {
      ...
    } ]
  else []
in

let newnodes_goodmatch st fm g =
  match fm with
  | Eapp (s, args, _) ->
     List.flatten (List.map (fun n -> mk_goodmatch fm n) (Index.find_neg s))
  | Enot (Eapp (s, args, _), _) ->
     List.flatten (List.map (fun p -> mk_goodmatch p fm) (Index.find_pos s))
  | Eall (v, t, p, _) ->
     List.flatten (List.map (fun n -> mk_goodmatch fm n) (Index.find_neg "A."))
  | Enot (Eall (v, t, p, _), _) ->
     List.flatten (List.map (fun p -> mk_goodmatch p fm) (Index.find_pos "A."))
  | Eex (v, t, p, _) ->
     List.flatten (List.map (fun n -> mk_goodmatch fm n) (Index.find_neg "E."))
  | Enot (Eex (v, t, p, _), _) ->
     List.flatten (List.map (fun p -> mk_goodmatch p fm) (Index.find_pos "E."))
  | _ -> (st, false)
;;

end goodmatch stuff *)

let newnodes_preunif st fm g _ =
  match fm with
  | Enot (Eapp (s, _, _), _) ->
      let do_match st (p, g2) =
        let f st1 (m, e) = fst (make_inst st1 m e (min g g2)) in
        List.fold_left f st (preunify p fm)
      in
      List.fold_left do_match st (Index.find_pos s), false
  | Eapp (s, _, _) ->
      let do_match st (p, g2) =
        let f st1 (m, e) = fst (make_inst st1 m e (min g g2)) in
        List.fold_left f st (preunify p fm)
      in
      List.fold_left do_match st (Index.find_neg s), false
  | _ -> (st, false)
;;

let newnodes_useless st fm g _ =
  match fm with
  | Evar _ | Enot (Evar _, _)
  | Etau _ | Enot (Etau _, _)
    -> st, true

  | Etrue | Enot (Efalse, _)
    -> st, true

(*  NOTE: meta can happen with TLA+
  | Emeta _ | Elam _ | Enot ((Emeta _ | Elam _), _)
    ->
      if !Error.warnings_flag then begin
        eprintf "add_nodes: unexpected formula meta or lambda ";
        Print.expr (Print.Chan stderr) fm;
        eprintf "\n";
      end;
      st, true
*)
  | _ -> (st, false)
;;

let newnodes_extensions state fm g fms =
  let (newnodes, stop) = Node.relevant (Extension.newnodes fm g fms) in
  let insert_node s n = {(*s with*) queue = insert s.queue n} in
  let state2 = List.fold_left insert_node state newnodes in
  (state2, stop)
;;

let prove_rules = [
  newnodes_absurd;
  newnodes_closure;
  newnodes_extensions;
  newnodes_jtree;
  newnodes_alpha;
  newnodes_beta;
  newnodes_eq_str;
  newnodes_delta;
  newnodes_gamma;
  newnodes_unfold;
  newnodes_refl;
  newnodes_preunif;
  newnodes_match_congruence;
  newnodes_match_trans;
  newnodes_match_sym;
  newnodes_match;
  newnodes_useless;
];;

(* TODO permettre aux extensions de modifier l'etat ? *)

let add_nodes rules st fm g fms =
  let combine (state, stop) f =
    if stop then (state, true) else f state fm g fms
  in
  let (st1, _) = List.fold_left combine (st, false) rules in
  st1
;;

let rec reduce_list accu l =
  match l with
  | Enot (Efalse, _) :: t
  | Etrue :: t
  | Enot (Eapp ("TLA.in", [_; Evar ("TLA.emptyset", _)], _), _) :: t
    -> reduce_list accu t
  | Eapp (s, [e1; e2], _) :: t when Expr.equal e1 e2 && Eqrel.refl s ->
      reduce_list accu t
  | Eapp (s, [e1; e2], _) as f :: t when Eqrel.sym s ->
      let g = eapp (s, [e2; e1]) in
      if Index.member f || Index.member g
         || List.exists (Expr.equal f) accu || List.exists (Expr.equal g) accu
      then reduce_list accu t
      else reduce_list (f :: accu) t
  | Enot (Eapp (s, [e1; e2], _), _) as f :: t when Eqrel.sym s ->
     let g = enot (eapp (s, [e2; e1])) in
     if Index.member f || Index.member g
        || List.exists (Expr.equal f) accu || List.exists (Expr.equal g) accu
     then reduce_list accu t
     else reduce_list (f :: accu) t
  | f :: t ->
     if Index.member f || List.exists (Expr.equal f) accu
     then reduce_list accu t
     else reduce_list (f :: accu) t
  | [] -> accu
;;

let reduce_branches n =
  let reduced = Array.map (reduce_list []) n.nbranches in
  let rec array_exists f a i =
    if i >= Array.length a then false
    else if f a.(i) then true
    else array_exists f a (i+1)
  in
  if array_exists (function [] -> true | _ -> false) reduced 0
  then None
  else Some { n with nbranches = reduced }
;;

let sort_uniq l =
  let l1 = List.sort Expr.compare l in
  let rec uniq l accu =
    match l with
    | [] | [_] -> l @ accu
    | x :: (y :: _ as t) when Expr.equal x y -> uniq t accu
    | x :: t -> uniq t (x :: accu)
  in
  uniq l1 []
;;

let rec not_meta_eq e =
  match e with
  | Eapp ("=", ([Emeta _; _] | [_; Emeta _]), _) -> false
  | Eapp (_, ([Evar ("_", _); Emeta _; _] | [_; Emeta _]), _) ->
     false (* FIXME HACK see ext_focal.ml *)
  | Eand (e1, e2, _)
  | Eor (e1, e2, _)
  -> not_meta_eq e1 || not_meta_eq e2
  | _ -> true
;;

let get_meta_weight e = if get_metas e =%= [] then 1 else 0;;

let count_meta_list l =
  let l = List.filter not_meta_eq l in
  let l = sort_uniq (List.flatten (List.map get_metas l)) in
  List.fold_left (fun x y -> x + get_meta_weight y) 0 l
;;

let rec not_trivial e =
  match e with
  | Enot (Eapp ("=", ([Emeta _; _] | [_; Emeta _]), _), _) -> false
  | Enot (Eapp ("TLA.in", [Emeta _; Evar ("TLA.emptyset", _)], _), _) -> true
  | Enot (Eapp ("TLA.in", [Emeta _; Evar _], _), _) -> false
  | Eand (e1, e2, _) | Eor (e1, e2, _) -> not_trivial e1 || not_trivial e2
  | _ -> true
;;

let count_nontrivial l = List.length (List.filter not_trivial l);;

let rndstate = ref (Random.State.make [| 0 |]);;

let find_open_branch node brstate =
  let last = Array.length brstate - 1 in
  if brstate =%= [| |] then None
  else if brstate.(last) =%= Open
          && List.exists not_meta_eq node.nbranches.(last)
    then Some last
  else begin
    let rec loop accu i =
      if i < 0 then accu
      else if brstate.(i) =%= Open then loop (i::accu) (i-1)
      else loop accu (i-1)
    in
    let open_branches = loop [] last in
    match open_branches with
    | [] -> None
    | [i] -> Some i
    | l ->
        let score i =
          let fs = node.nbranches.(i) in
          let f accu x = accu + Expr.size x in
          let s = List.fold_left f 0 fs in
          (fs, count_nontrivial fs, count_meta_list fs, s, i)
        in
        let l1 = List.rev_map score l in
        let cmp (fs1, nt1, len1, size1, _) (fs2, nt2, len2, size2, _) =
          if nt1 =%= 0 then 1
          else if nt2 =%= 0 then -1
          else if len1 <> len2 then len2 - len1
          else size1 - size2
(*
          match node.nrule with
          | P_NotP _ | P_NotP_sym _ ->
             if len1 =%= len2 then size1 - size2
             else len1 - len2
          | _ ->
            if len1 =%= len2
            then size1 - size2
            else len2 - len1
*)
        in
        let l2 = List.sort cmp l1 in
        if !Globals.random_flag then begin
          let l = List.length l2 in
          let n = Random.State.int !rndstate l in
          match List.nth l2 n with (_, _, _, _, i) -> Some i
        end else begin
          match l2 with
          | (_, _, _, _, i) :: _ -> Some i
          | _ -> assert false
        end
  end
;;

let dummy_proof = {
  mlconc = [];
  mlrule = False;
  mlhyps = [| |];
  mlrefc = 0;
};;

let is_equiv r =
  match r with
  | Equiv _ | NotEquiv _ -> true
  | _ -> false
;;

let add_virtual_branch n =
  let len = Array.length n.nbranches in
  if len < 2 then begin
    (n, Array.make len Open)
  end else begin
    let branches = Array.make (len+1) [] in
    let brstate = Array.make (len+1) Open in
    for i = 0 to len - 1 do
      branches.(i) <- n.nbranches.(i);
      let has_metas fm = Expr.count_metas fm > 0 in
      let with_metas = List.filter has_metas n.nbranches.(i) in
      branches.(len) <- with_metas @@ branches.(len);
    done;

    if List.length (List.filter not_trivial branches.(len)) < 2
       || is_equiv n.nrule
    then begin
      brstate.(len) <- Closed dummy_proof;
    end;
    ({n with nbranches = branches}, brstate)
  end
;;

let remove_virtual_branch n brst =
  let len = Array.length n.nbranches in
  if len < 2 then begin
    (n, brst)
  end else begin
    let branches = Array.sub n.nbranches 0 (len-1) in
    let brstate = Array.sub brst 0 (len-1) in
    ({n with nbranches = branches}, brstate)
  end
;;

let good_lemma rule =
  match rule with
  | Close _ | Close_refl _ | Close_sym _ | False | NotTrue -> false
  | _ -> true
;;

(* there is no [Open] in [branches]; make a proof node *)
let make_result n nbranches =
  let concs = ref []
  and proofs = ref []
  in
  for i = 0 to Array.length nbranches - 1 do
    match nbranches.(i) with
    | Open | Backtrack -> assert false
    | Closed p ->
        proofs := p :: !proofs;
        concs := union (diff p.mlconc n.nbranches.(i)) !concs;
  done;
  assert (List.length !proofs == Array.length n.nbranches);
  let prf_node = {
    mlconc = union n.nconc !concs;
    mlrule = n.nrule;
    mlhyps = Array.of_list (List.rev !proofs);
    mlrefc = 1;
  } in
  incr Globals.proof_nodes;
  if good_lemma n.nrule then begin
    Index.add_proof prf_node;
  end;
  Closed prf_node
;;

let good_head q =
  match head q with
  | None -> true
  | Some node -> good_lemma node.nrule
;;

exception NoProof;;
exception LimitsExceeded;;

let progress_period = ref 100;;
let progress_counter = ref !progress_period;;
let progress_last = ref 0.0;;
let period_base = 0.3;;

let periodic c =
  progress_counter := !progress_period;
  Progress.do_progress (fun () -> ()) c;
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  let tm = Sys.time () in
  if tm > !progress_last +. 0.001 then begin
    let new_period = float !progress_period *. period_base
                     /. (tm -. !progress_last) in
    progress_period := int_of_float new_period;
  end;
  if !progress_period < 1 then progress_period := 1;
  progress_last := tm;
  if tm > !Globals.time_limit then begin
    Progress.end_progress "";
    Error.err "could not find a proof within the time limit";
    flush stderr;
    raise LimitsExceeded;
  end;
  if float heap_size *. float Sys.word_size /. 8. > !Globals.size_limit
  then begin
    Progress.end_progress "";
    Error.err "could not find a proof within the memory size limit";
    flush stderr;
    raise LimitsExceeded;
  end;
  if !steps > !Globals.step_limit then begin
    Progress.end_progress "";
    Error.err "could not find a proof within the inference steps limit";
    flush stderr;
    raise LimitsExceeded;
  end;
;;

let progress () =
  decr progress_counter;
  if !progress_counter < 0 then periodic '*';
;;

let prove_fail () =
  let is_logic e =
    match e with
    | Eand _ | Eor _ | Eimply _ | Eequiv _ | Efalse | Etrue
    | Eall _ | Eex _ | Etau _ | Elam _ | Enot (Enot _, _)
    -> true
    | _ -> false
  in
  let f (e, _) =
    match e with
    | _ when is_logic e -> ()
    | Enot (e1, _) when is_logic e1 -> ()
    | _ -> Print.expr_soft (Print.Chan stdout) e; printf "\n";
  in
  if !Globals.debug_flag then Step.forms "NO PROOF" (Index.get_all ());
  Error.err "exhausted search space without finding a proof";
  flush stderr;
  printf "(* Current branch:\n";
  List.iter f (Index.get_all ());
  printf "*)\n";
  raise NoProof
;;

type rule =
  state -> expr -> int -> (expr * int) list -> state * bool
and params = {
  rules : rule list;
  fail : unit -> branch_state;
  progress : unit -> unit;
  end_progress : string -> unit;
};;

let rec refute_aux prm stk st forms =
  prm.progress ();
  match forms with
  | [] ->
      if good_head st.queue then begin
        match Index.search_proof () with
        | Some p -> p.mlrefc <- p.mlrefc + 1; unwind prm stk (Closed p)
        | None -> next_node prm stk st
      end else begin
        next_node prm stk st
      end
  | (Etrue, _) :: fms
  | (Enot (Efalse, _), _) :: fms
    -> refute_aux prm stk st fms
  | (Eapp (s, [e1; e2], _), _) :: fms when Eqrel.refl s && Expr.equal e1 e2 ->
      refute_aux prm stk st fms
  | (fm, g) :: fms ->
      Index.add fm g;
      Extension.add_formula fm;
      refute_aux prm stk (add_nodes prm.rules st fm g fms) fms

and refute prm stk st forms =
  Step.forms "refute" forms;
  refute_aux prm stk st forms

and next_node prm stk st =
  prm.progress ();
  incr Globals.inferences;
  match remove st.queue with
  | None -> prm.fail ()
  | Some (n, q1) ->
      let st1 = {(*st with*) queue = q1} in
      match reduce_branches n with
      | Some n1 ->
(*
          let (n2, brstate) = add_virtual_branch n1 in
          next_branch stk n2 st1 brstate
*)
         let brstate = Array.make (Array.length n.nbranches) Open in
         next_branch prm stk n1 st1 brstate
      | None -> next_node prm stk st1

and next_branch prm stk n st brstate =
  Step.rule "next_branch" n.nrule;
  match find_open_branch n brstate with
  | Some i ->
      let fr = {node = n; state = st; brst = brstate; curbr = i} in
      incr cur_depth;
      if !cur_depth > !top_depth then top_depth := !cur_depth;
      if !cur_depth > !max_depth then begin
        unwind prm stk Backtrack
      end else begin
        refute prm (fr :: stk) st
               (List.map (fun x -> (x, n.ngoal)) n.nbranches.(i))
      end
  | None ->
(*
      let (n1, brstate1) = remove_virtual_branch n brstate in
      let result = make_result n1 brstate1 in
*)
      let result = make_result n brstate in
      unwind prm stk result

and unwind prm stk res =
  prm.progress ();
  decr cur_depth;
  match stk with
  | [] -> res
  | fr :: stk1 ->
      Step.rule "unwind" fr.node.nrule;
      let f x =
        if Index.member x then begin (* we can unwind before adding all forms *)
          Extension.remove_formula x;
          Index.remove x;
        end;
      in
      List.iter f (List.rev fr.node.nbranches.(fr.curbr));
      begin match res with
      | Closed p when disjoint fr.node.nbranches.(fr.curbr) p.mlconc ->
          unwind prm stk1 res
      | Backtrack -> unwind prm stk1 res
      | Closed _ ->
          fr.brst.(fr.curbr) <- res;
          next_branch prm stk1 fr.node fr.state fr.brst
      | Open -> assert false
      end;
;;

let rec reduce_initial_list accu l =
  match l with
  | [] -> accu
  | (f, p) as fp :: t ->
      if List.exists (fun (e, _) -> Expr.equal f e) accu
      then reduce_initial_list accu t
      else reduce_initial_list (fp :: accu) t
;;

let ticker finished () =
  let tm = Sys.time () in
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  Progress.do_progress begin fun () ->
    eprintf "depth %5d/%d  search %d  proof %d  \
             lemma %d  size %dM  time %.0f\n"
            !cur_depth !top_depth !Globals.inferences !Globals.proof_nodes
            !Globals.stored_lemmas (heap_size / 1_000_000) tm;
    Expr.print_stats stderr;
  end '#';
  if not finished then periodic '#';
;;

let rec iter_refute prm rl =
  match refute prm [] {queue = empty} rl with
  | Backtrack ->
      max_depth := 2 * !max_depth;
      Progress.do_progress begin fun () ->
        eprintf "increase max_depth to %d\n" !max_depth;
      end '*';
      iter_refute prm rl;
  | x -> x
;;

let prove prm defs l =
  if !Globals.random_flag then begin
    rndstate := Random.State.make [| !Globals.random_seed |];
    max_depth := 100;
  end;
  List.iter Index.add_def defs;
  let al = Gc.create_alarm (ticker false) in
  let rl = reduce_initial_list [] l in
  Globals.inferences := 0;
  Globals.proof_nodes := 0;
  cur_depth := 0;
  top_depth := 0;
  try
    match iter_refute prm rl with
    | Closed p ->
        Gc.delete_alarm al;
        ticker true ();
        prm.end_progress "";
        p
    | Open | Backtrack -> assert false
  with e ->
    prm.end_progress " no proof";
    raise e
;;

let default_params = {
  rules = prove_rules;
  fail = prove_fail;
  progress = progress;
  end_progress = Progress.end_progress;
};;
