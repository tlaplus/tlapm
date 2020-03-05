(*  Copyright 2004 INRIA  *)

open Printf;;

open Expr;;
open Llproof;;
open Namespace;;

exception Found of expr;;

let get_diff e1 e2 =
  let rec spin x y =
    if Expr.equal x y then () else
    match x, y with
    | Eapp (s1, args1, _), Eapp (s2, args2, _)
      when s1 = s2 && List.length args1 = List.length args2 ->
       List.iter2 spin args1 args2
    | Emeta (e1, _), Emeta (e2, _)
    | Enot (e1, _), Enot (e2, _)
      -> spin e1 e2
    | Eand (e1a, e1b, _), Eand (e2a, e2b, _)
    | Eor (e1a, e1b, _), Eor (e2a, e2b, _)
    | Eimply (e1a, e1b, _), Eimply (e2a, e2b, _)
    | Eequiv (e1a, e1b, _), Eequiv (e2a, e2b, _)
      -> spin e1a e2a; spin e1b e2b

    | Etrue, Etrue -> ()
    | Efalse, Efalse -> ()
    | Eall (v1, t1, e1, _), Eall (v2, t2, e2, _)
    | Eex (v1, t1, e1, _), Eex (v2, t2, e2, _)
    | Etau (v1, t1, e1, _), Etau (v2, t2, e2, _)
    | Elam (v1, t1, e1, _), Elam (v2, t2, e2, _)
      when Expr.equal v1 v2 && t1 = t2 ->
      spin e1 e2

    | _, _ -> raise (Found x)
  in
  try spin e1 e2; raise Not_found with Found e -> e
;;

let rec p_list init printer sep oc l =
  match l with
  | [] -> ()
  | [x] -> fprintf oc "%s%a" init printer x;
  | h::t ->
      fprintf oc "%s%a%s" init printer h sep;
      p_list init printer sep oc t;
;;

let p_type oc t =
  match t with
  | t when t = univ_name -> fprintf oc "%s" t;
  | "" -> fprintf oc "_";
  | s -> fprintf oc "%s" s;
;;

let rec decompose_lambda e =
  match e with
  | Elam (Evar (v, _), t, b, _) ->
     let bindings, body = decompose_lambda b in
     ((v, t) :: bindings), body
  | Elam _ -> assert false
  | _ -> [], e
;;

let p_binding oc (v, t) =
  fprintf oc "(%s : %a)" v p_type t
;;

let p_id_list oc l = p_list " " (fun oc x -> fprintf oc "%s" x) "" oc l;;

let rec p_expr oc e =
  let poc fmt = fprintf oc fmt in
  match e with
  | Evar (v, _) when Mltoll.is_meta v ->
      poc "%s" (Coqterm.synthesize v);
  | Evar (v, _) ->
      poc "%s" v;
  | Eapp ("=", [e1; e2], _) ->
      poc "(%a = %a)" p_expr e1 p_expr e2;
  | Eapp ("=", l, _) ->
      p_expr oc (eapp ("@eq _", l));
  | Eapp ("$match", e1 :: l, _) ->
      poc "match %a with%a end" p_expr e1 p_cases l;
  | Eapp ("$fix", Elam (Evar (f, _), _, body, _) :: l, _) ->
      let bindings, expr = decompose_lambda body in
      poc "((fix %s%a := %a)%a)" f (p_list " " p_binding "") bindings
          p_expr expr (p_list " " p_expr "") l
  | Eapp ("FOCAL.ifthenelse", [e1; e2; e3], _) ->
      poc "(if %a then %a else %a)" p_expr e1 p_expr e2 p_expr e3;
  | Eapp ("$string", [Evar (v, _)], _) ->
      poc "%s" v;
  | Eapp ("*", [e1; e2], _) ->
      poc "%a*%a" p_expr e1 p_expr e2;
  | Eapp ("%", [e1; e2], _) ->
      poc "%a%%%a" p_expr e1 p_expr e2;
  | Eapp (f, l, _) ->
      poc "(%s%a)" f p_expr_list l;
  | Enot (e, _) ->
      poc "(~%a)" p_expr e;
  | Eand (e1, e2, _) ->
      poc "(%a/\\%a)" p_expr e1 p_expr e2;
  | Eor (e1, e2, _) ->
      poc "(%a\\/%a)" p_expr e1 p_expr e2;
  | Eimply (e1, e2, _) ->
      poc "(%a->%a)" p_expr e1 p_expr e2;
  | Eequiv (e1, e2, _) ->
      poc "(%a<->%a)" p_expr e1 p_expr e2;
  | Etrue ->
      poc "True";
  | Efalse ->
      poc "False";
  | Eall (Evar (x, _), t, e1, _) ->
      poc "(forall %s : %a, %a)" x p_type t p_expr e1;
  | Eall _ -> assert false
  | Eex (Evar (x, _), t, e1, _) ->
      poc "(exists %s : %a, %a)" x p_type t p_expr e1;
  | Eex _ -> assert false
  | Elam (Evar (x, _), t, e1, _) ->
      poc "(fun %s : %a => %a)" x p_type t p_expr e1;
  | Elam _ -> assert false
  | Emeta _ -> assert false
  | Etau _ -> poc "%s" (Index.make_tau_name e);

and p_expr_list oc l = p_list " " p_expr "" oc l;

and p_cases oc l = p_list " " (p_case []) "" oc l;

and p_case accu oc e =
  match e with
  | Eapp ("$match-case", [Evar (constr, _); body], _) ->
     fprintf oc "| %s%a => %a" constr p_id_list (List.rev accu) p_expr body;
  | Elam (Evar (v, _), _, body, _) ->
     p_case (v :: accu) oc body
  | _ -> assert false
;;

let rec p_nand oc l =
  match l with
  | e :: t -> fprintf oc "%a -> " p_expr e; p_nand oc t;
  | [] -> fprintf oc "False";
;;

let rec p_bound_vars oc l =
  match l with
  | (ty, arg) :: t ->
     fprintf oc " (%a : %a)" p_expr arg p_type ty;
     p_bound_vars oc t;
  | [] -> ()
;;

let rec p_forall oc l =
  match l with
  | _ :: _ -> fprintf oc "forall%a, " p_bound_vars l;
  | [] -> ()
;;

let get_goals concl =
  List.filter (fun x -> Coqterm.is_goal x || not (Coqterm.is_mapped x)) concl
;;

let declare_lemma oc name params concl =
  fprintf oc "assert (%s : %a%a).\n" name p_forall params
          p_nand (get_goals concl);
;;

let declare_theorem oc name params concl phrases =
  let nconcl, script_prefix =
    match get_goals concl with
    | [ Enot (e, _) ] -> e, ""
    | [] ->
        begin match Coqterm.get_goal phrases with
        | None -> efalse, ""
        | Some (Enot (g, _)) -> g, "apply NNPP; intro.\n"
        | _ -> assert false
        end
    | _ -> assert false
  in
  fprintf oc "Theorem %s : %a%a.\n" name p_forall params p_expr nconcl;
  fprintf oc "Proof.\n%s" script_prefix;
  Coqterm.print_use_all oc phrases;
;;

let getname e = Coqterm.getname e ;;

let p_name_list oc l =
  p_list " " (fun oc e -> fprintf oc "%s" (getname e)) "" oc l;
;;

let p_start_lemma oc nvars conc =
  fprintf oc "do %d intro. intros%a.\n" nvars p_name_list conc
;;

let p_start_thm oc conc =
  match get_goals conc with
  | [] -> ()
  | [e] -> fprintf oc "apply NNPP. intro %s.\n" (getname e);
  | _ -> assert false
;;

let p_end oc = fprintf oc "Qed.\n";;

let p_intro oc e =
  fprintf oc "zenon_intro %s; " (getname e);
;;

let p_intros oc l =
  List.iter (p_intro oc) l;
  fprintf oc "idtac";
;;

let p_rev_app oc (f, args) =
  fprintf oc "(%s%a)" f p_expr_list (List.rev args)
;;

let apply_alpha oc lem h0 h1 h2 =
  fprintf oc "apply (zenon_%s_s _ _ %s). zenon_intro %s. zenon_intro %s.\n"
             lem (getname h0) (getname h1) (getname h2);
;;

let apply_beta oc lem h0 h1 h2 =
  fprintf oc "apply (zenon_%s_s _ _ %s); [ zenon_intro %s | zenon_intro %s ].\n"
             lem (getname h0) (getname h1) (getname h2);
;;

let apply_beta2 oc lem h0 h1a h1b h2a h2b =
  fprintf oc "apply (zenon_%s_s _ _ %s); \
              [ zenon_intro %s; zenon_intro %s \
                | zenon_intro %s; zenon_intro %s ].\n"
             lem (getname h0) (getname h1a) (getname h1b)
             (getname h2a) (getname h2b);
;;

let notmeta x =
  match x with
  | Evar (v, _) -> not (Mltoll.is_meta v)
  | _ -> true
;;

let p_rule oc r =
  let poc fmt = fprintf oc fmt in
  match r with
  | Rconnect (And, e1, e2) ->
      apply_alpha oc "and" (eand (e1, e2)) e1 e2
  | Rconnect (Or, e1, e2) ->
      apply_beta oc "or" (eor (e1, e2)) e1 e2
  | Rconnect (Imply, e1, e2) ->
      apply_beta oc "imply" (eimply (e1, e2)) (enot e1) e2
  | Rconnect (Equiv, e1, e2) ->
      apply_beta2 oc "equiv" (eequiv (e1, e2)) (enot e1) (enot e2) e1 e2
  | Rnotconnect (And, e1, e2) ->
      apply_beta oc "notand" (enot (eand (e1, e2))) (enot e1) (enot e2)
  | Rnotconnect (Or, e1, e2) ->
      apply_alpha oc "notor" (enot (eor (e1, e2))) (enot e1) (enot e2)
  | Rnotconnect (Imply, e1, e2) ->
      apply_alpha oc "notimply" (enot (eimply (e1, e2))) e1 (enot e2)
  | Rnotconnect (Equiv, e1, e2) ->
      apply_beta2 oc "notequiv" (enot (eequiv (e1, e2)))
                  (enot e1) e2 e1 (enot e2)
  | Rextension ("", name, args, conc, hyps) ->
      poc "apply (%s_s%a%a)" name p_expr_list args p_name_list conc;
      begin match hyps with
      | [] -> poc ".\n";
      | _ -> poc "; [ %a ].\n" (p_list "" p_intros " | ") hyps;
      end;
  | Rextension (ext, lemma, args, cons, hyps) ->
     Extension.p_rule_coq ext oc r;
  | Rnotnot (p as e) ->
      poc "apply %s. zenon_intro %s.\n" (getname (enot (enot e))) (getname e);
  | Rex (Eex (vx, ty, e, _) as p, t) ->
      let h0 = getname p in
      let zz = etau (vx, ty, e) in
      let zzn = Index.make_tau_name zz in
      let h1 = getname (substitute [(vx, zz)] e) in
      poc "elim %s. zenon_intro %s. zenon_intro %s.\n" h0 zzn h1;
  | Rex _ -> assert false
  | Rnotall (Eall (vx, ty, e, _) as p, t) ->
      let h0 = getname (enot p) in
      let zz = etau (vx, ty, enot (e)) in
      let zzn = Index.make_tau_name zz in
      let h1 = getname (enot (substitute [(vx, zz)] e)) in
      poc "apply %s. zenon_intro %s. apply NNPP. zenon_intro %s.\n" h0 zzn h1;
  | Rnotall _ -> assert false
  | Rall (Eall (x, _, e, _) as p, t) ->
      let h0 = getname p in
      let h1 = getname (substitute [(x, t)] e) in
      poc "generalize (%s %a). zenon_intro %s.\n" h0 p_expr t h1;
  | Rall _ -> assert false
  | Rnotex (Eex (x, _, e, _) as p, t) ->
      let h0 = getname (enot p) in
      let h1 = getname (enot (substitute [(x, t)] e)) in
      poc "apply %s. exists %a. apply NNPP. zenon_intro %s.\n" h0 p_expr t h1;
  | Rnotex _ -> assert false
  | Rlemma (name, args) ->
      let args1 = List.filter notmeta args in
      poc "apply (%s%a); trivial.\n" name p_expr_list args1;
  | Rcut (e) ->
      let h0 = getname e in
      let h1 = getname (enot e) in
      poc "elim (classic %a); [ zenon_intro %s | zenon_intro %s ].\n"
          p_expr e h0 h1;
  | Raxiom (e) ->
      let h0 = getname e in
      let h1 = getname (enot e) in
      poc "exact (%s %s).\n" h1 h0;
  | Rdefinition (_, s, a, b, None, c, h) ->
      poc "assert (%s : %a). exact %s.\n" (getname h) p_expr h (getname c);
  | Rdefinition (_, s, a, b, Some v, c, h) ->
      let args =
        match get_diff c h with
        | Eapp (ss, args, _) when ss = s -> args
        | _ -> assert false
      in
      let vv = evar v in
      let rec find_recarg l1 l2 =
        match l1, l2 with
        | h1::t1, h2::t2 -> if h1 = vv then h2 else find_recarg t1 t2
        | _ -> assert false
      in
      let recarg = find_recarg a args in
      poc "assert (%s: %a). " (getname h) p_expr h;
      (* Fix bug 37: do not destruct a constructor value. *)
      if not (Coqterm.is_constr recarg) then begin
        poc "destruct %a; " p_expr (find_recarg a args) ;
        poc "simpl; auto.\n"
      end else (* Fix bug 59. *)
        poc "exact %s.\n" (getname c)
  | Rnotequal (Eapp (f, args1, _) as e1, (Eapp (g, args2, _) as e2)) ->
     assert (f = g);
     let f a1 a2 =
       let eq =
         match a1, a2 with
         | Evar ("_", _), _ | _, Evar ("_", _) ->
             eapp ("=", [evar "true"; evar "true"])
         | e1, e2 when Expr.equal e1 e2 ->
             eapp ("=", [evar "true"; evar "true"])
         | _ -> eapp ("=", [a1; a2])
       in
       let neq = enot (eapp ("=", [a1; a2])) in
       poc "cut (%a); [idtac | apply NNPP; zenon_intro %s].\n"
           p_expr eq (getname neq);
     in
     List.iter2 f (List.rev args1) (List.rev args2);
     let goal = enot (eapp ("=", [e1; e2])) in
     poc "generalize %s; simpl.\n" (getname goal); (* hack *)
     poc "congruence.\n";
  | Rnotequal _ -> assert false
  | Rpnotp ((Eapp (f, args1, _) as ff), Enot ((Eapp (g, args2, _) as gg), _)) ->
     assert (f = g);
     poc "cut (%a = %a).\n" p_expr ff p_expr gg;
     poc "intro %s_pnotp.\n" Namespace.dummy_prefix;
     poc "apply %s.\n" (getname (enot gg));
     poc "try rewrite <- %s_pnotp.\n" Namespace.dummy_prefix;
     poc "exact %s.\n" (getname ff);
     let f a1 a2 =
       let eq = eapp ("=", [a1; a2]) in
       let neq = enot eq in
       poc "cut (%a); [idtac | apply NNPP; zenon_intro %s].\n"
           p_expr eq (getname neq);
     in
     List.iter2 f (List.rev args1) (List.rev args2);
     poc "congruence.\n";
  | Rpnotp _ -> assert false
  | Rnoteq e ->
      poc "apply %s. apply refl_equal.\n" (getname (enot (eapp ("=", [e; e]))));
  | Reqsym (e, f) ->
      poc "apply %s. apply sym_equal. exact %s.\n"
          (getname (enot (eapp ("=", [f; e]))))
          (getname (eapp ("=", [e; f])));
  | Rnottrue ->
      poc "exact (%s I).\n" (getname (enot (etrue)));
  | Rfalse ->
      poc "exact %s.\n" (getname efalse);
  | RcongruenceLR (p, a, b) ->
      let c1 = apply p a in
      let c2 = eapp ("=", [a; b]) in
      let h = apply p b in
      poc "apply (zenon_congruence_lr_s _ %a %a %a %s %s). zenon_intro %s.\n"
          p_expr p p_expr a p_expr b (getname c1) (getname c2) (getname h);
  | RcongruenceRL (p, a, b) ->
      let c1 = apply p a in
      let c2 = eapp ("=", [b; a]) in
      let h = apply p b in
      poc "apply (zenon_congruence_rl_s _ %a %a %a %s %s). zenon_intro %s.\n"
          p_expr p p_expr a p_expr b (getname c1) (getname c2) (getname h);
;;

let rec p_tree oc proof =
  p_rule oc proof.rule;
  List.iter (p_tree oc) proof.hyps;
;;

let p_script_lemma oc nvars proof =
  p_start_lemma oc nvars (get_goals proof.conc);
  p_tree oc proof;
;;

let p_script_thm oc proof =
  p_start_thm oc (get_goals proof.conc);
  p_tree oc proof;
  p_end oc;
;;

let rec p_lemmas oc l =
  match l with
  | [] -> ()
  | lem :: t ->
     let params = List.filter (fun (ty, v) -> notmeta v) lem.params in
     declare_lemma oc lem.name params lem.proof.conc;
     p_script_lemma oc (List.length params) lem.proof;
     fprintf oc "(* end of lemma %s *)\n" lem.name;
     p_lemmas oc t;
;;

let p_theorem oc phrases l =
  match l with
  | [] -> assert false
  | thm :: lemmas ->
     let params = List.filter (fun (ty, v) -> notmeta v) thm.params in
     declare_theorem oc thm.name params thm.proof.conc phrases;
     p_lemmas oc (List.rev lemmas);
     p_script_thm oc thm.proof;
;;

let output oc phrases ppphrases llp =
  try
    Coqterm.init_mapping phrases;
    Coqterm.init_induct ppphrases;
    if !Globals.ctx_flag then Coqterm.declare_context oc phrases;
    if not !Globals.quiet_flag then fprintf oc "(* BEGIN-PROOF *)\n";
    p_theorem oc phrases (List.rev llp);
    if not !Globals.quiet_flag then fprintf oc "(* END-PROOF *)\n";
    !Coqterm.constants_used
  with
  | Coqterm.Cannot_infer ty ->
      let msg = sprintf "cannot infer a value for a variable of type %s" ty in
      Error.err msg;
      raise Error.Abort
;;
