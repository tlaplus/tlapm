(*  Copyright 2004 INRIA  *)

open Expr;;
open Mlproof;;
open Namespace;;
open Printf;;


type output = Buff of Buffer.t | Chan of out_channel;;

let mybuf = Buffer.create 100;;
let mychan = ref stdout;;
let flush () = Buffer.output_buffer !mychan mybuf; Buffer.clear mybuf;;

let printf = ();; (* FIXME DEBUG *)

let oprintf o fmt (* ... *) =
  match o with
  | Buff b -> bprintf b fmt (* ... *)
  | Chan c ->
     flush ();
     mychan := c;
     bprintf mybuf fmt (* ... *)
;;

let buf o =
  match o with
  | Buff b -> b
  | Chan c -> mybuf
;;

let is_letter c =
  match c with
  | 'A' .. 'Z' | 'a' .. 'z' -> true
  | _ -> false
;;

let print_var b v =
  match v with
  | Evar (s, _) -> bprintf b "%s" s
  | _ -> assert false
;;

let print_vartype b (v, t) =
  if t = univ_name
  then print_var b v
  else bprintf b "%a:\"%s\" " print_var v t
;;

let rec expr o ex =
  let pr f = oprintf o f in
  match ex with
  | Evar (v, _) -> pr "%s" v;

  | Emeta (e, _) -> pr "%s%d" meta_prefix (Index.get_number e);
  | Eapp (s, es, _) ->
      pr "(%s" s; List.iter (fun x -> pr " "; expr o x) es; pr ")";
  | Enot (e, _) -> pr "(-. "; expr o e; pr ")";
  | Eand (e1, e2, _) ->
      pr "(/\\ "; expr o e1; pr " "; expr o e2; pr ")";
  | Eor (e1, e2, _) ->
      pr "(\\/ "; expr o e1; pr " "; expr o e2; pr ")";
  | Eimply (e1, e2, _) ->
      pr "(=> "; expr o e1; pr " "; expr o e2; pr ")";
  | Eequiv (e1, e2, _) ->
      pr "(<=> "; expr o e1; pr " "; expr o e2; pr ")";
  | Etrue -> pr "(True)";
  | Efalse -> pr "(False)";
  | Eall (v, t, e, _) when t = univ_name ->
      pr "(A. ((%a) " print_var v; expr o e; pr "))";
  | Eall (v, t, e, _) ->
      pr "(A. ((%a \"%s\") " print_var v t; expr o e; pr "))";
  | Eex (v, t, e, _) when t = univ_name ->
      pr "(E. ((%a) " print_var v; expr o e; pr "))";
  | Eex (v, t, e, _) ->
      pr "(E. ((%a \"%s\") " print_var v t; expr o e; pr "))";
  | Etau (v, t, e, _) when t = univ_name ->
      pr "(t. ((%a) " print_var v; expr o e; pr "))";
  | Etau (v, t, e, _) ->
      pr "(t. ((%a \"%s\") " print_var v t; expr o e; pr "))";
  | Elam (v, t, e, _) when t = univ_name ->
      pr "((%a) " print_var v; expr o e; pr ")";
  | Elam (v, t, e, _) ->
      pr "((%a \"%s\") " print_var v t; expr o e; pr ")";
;;

let expr o e =
  expr o e;
  flush ();
;;

let is_infix_op s =
  s <> "" && not (is_letter s.[0]) && s.[0] <> '$' && s.[0] <> '_'
;;

let rec expr_soft o ex =
  let pr f = oprintf o f in
  match ex with
  | Evar (v, _) -> pr "%s" v;
  | Emeta (e, _) -> pr "%s%d" meta_prefix (Index.get_number e);
  | Eapp (s, [e1; e2], _) when is_infix_op s ->
     pr "("; expr_soft o e1; pr " %s " s; expr_soft o e2; pr ")";
  | Eapp (s, es, _) ->
      pr "(%s" s;
      List.iter (fun x -> pr " "; expr_soft o x) es;
      pr ")";
  | Enot (Eapp ("=", [e1; e2], _), _) ->
      pr "("; expr_soft o e1; pr " != "; expr_soft o e2; pr ")";
  | Enot (e, _) -> pr "(-. "; expr_soft o e; pr ")";
  | Eand (e1, e2, _) ->
      pr "("; expr_soft o e1; pr " /\\ "; expr_soft o e2; pr ")";
  | Eor (e1, e2, _) ->
      pr "("; expr_soft o e1; pr " \\/ "; expr_soft o e2; pr ")";
  | Eimply (e1, e2, _) ->
      pr "("; expr_soft o e1; pr " => "; expr_soft o e2; pr ")";
  | Eequiv (e1, e2, _) ->
      pr "("; expr_soft o e1; pr " <=> "; expr_soft o e2; pr ")";
  | Etrue -> pr "True";
  | Efalse -> pr "False";
  | Eall (Evar (v, _), t, e, _) when t = univ_name ->
      pr "(All %s, " v; expr_soft o e; pr ")";
  | Eall (Evar (v, _), t, e, _) ->
      pr "(All %s:%s, " v t; expr_soft o e; pr ")";
  | Eall _ -> assert false
  | Eex (Evar (v, _), t, e, _) when t = univ_name ->
      pr "(Ex %s, " v; expr_soft o e; pr ")";
  | Eex (Evar (v, _), t, e, _) ->
      pr "(Ex %s:%s, " v t; expr_soft o e; pr ")";
  | Eex _ -> assert false
  | Etau _ as e -> pr "T_%d" (Index.get_number e);
  | Elam (Evar (v, _), t, e, _) when t = univ_name ->
      pr "(lambda %s, " v; expr_soft o e; pr ")";
  | Elam (Evar (v, _), t, e, _) ->
      pr "(lambda %s:%s, " v t; expr_soft o e; pr ")";
  | Elam _ -> assert false
;;

let expr_soft o e =
  expr_soft o e;
  flush ();
;;

let rec print_list b p_elem sep l =
  match l with
  | [] -> ()
  | [e] -> p_elem b e
  | h::t -> p_elem b h; bprintf b "%s" sep; print_list b p_elem sep t
;;

let phrase o ph =
  let pro f = oprintf o f in
  begin match ph with
  | Phrase.Hyp (n, e, p) -> pro "# %s:\n$%d " n p; expr o e; pro "\n";
  | Phrase.Def (DefReal (name, s, args, e, None)) ->
      pro "$def \"%s\" %s (" name s;
      print_list (buf o) print_var " " args;
      pro ") ";
      expr o e;
      pro "\n";
  | Phrase.Def (DefReal (name, s, args, e, Some v)) ->
      pro "$fixpoint \"%s\" %s %s (" name s v;
      print_list (buf o) print_var " " args;
      pro ") ";
      expr o e;
      pro "\n";
  | Phrase.Def (DefRec (eqn, s, args, e)) ->
      pro "$defrec %s (" s;
      print_list (buf o) print_var " " args;
      pro ") ";
      expr o e;
      pro " ";
      expr o eqn;
      pro "\n";
  | Phrase.Def (DefPseudo ((hyp, prio), s, args, e)) ->
      pro "#pseudo-def: ";
      expr o hyp;
      pro "\n$def %s (" s;
      print_list (buf o) print_var " " args;
      pro ") ";
      expr o e;
      pro "\n";
  | Phrase.Sig (sym, args, res) ->
      pro "$sig %s (" sym;
      List.iter (fun x -> pro " %s" x) args;
      pro ") %s\n" res;
  | Phrase.Inductive _ -> assert false (* FIXME *)
  end;
  flush ();
;;

let sequent o l =
  List.iter (fun x -> expr o x; oprintf o " ") l;
;;

let get_rule_name = function
  | Close e -> "Axiom", [e]
  | Close_refl (s, e) -> "Refl("^s^")", [e]
  | Close_sym (s, e1, e2) -> "Sym("^s^")", [e1; e2]
  | False -> "False", []
  | NotTrue -> "NotTrue", []
  | NotNot (e) -> "NotNot", [e]
  | NotAll (e) -> "NotAll", [e]
  | NotAllEx (e) -> "NotAllEx", [e]
  | Ex (e) -> "Exists", [e]
  | NotEqual (e1, e2) -> "NotEqual", [e1; e2]
  | And (e1, e2) -> "And", [e1; e2]
  | NotOr (e1, e2) -> "NotOr", [e1; e2]
  | NotImpl (e1, e2) -> "NotImply", [e1; e2]
  | All (e1, e2) -> "All", [e1; e2]
  | NotEx (e1, e2) -> "NotExists", [e1; e2]
  | Or (e1, e2) -> "Or", [e1; e2]
  | Impl (e1, e2) -> "Imply", [e1; e2]
  | NotAnd (e1, e2) -> "NotAnd", [e1; e2]
  | Equiv (e1, e2) -> "Equiv", [e1; e2]
  | NotEquiv (e1, e2) -> "NotEquiv", [e1; e2]
  | P_NotP (e1, e2) -> "P-NotP", [e1; e2]
  | P_NotP_sym (s, e1, e2) -> "P-NotP-sym("^s^")", [e1; e2]
  | Definition (DefReal (_, s, _, _, _), e, _) -> "Definition("^s^")", [e]
  | Definition (DefPseudo (_, s, _, _), e, _) -> "Definition-Pseudo("^s^")", [e]
  | Definition (DefRec (_, s, _, _), e, _) -> "Definition-Rec("^s^")", [e]
  | ConjTree e -> "ConjTree", [e]
  | DisjTree e -> "DisjTree", [e]
  | AllPartial (e1, s, n) -> "All-Partial", [e1]
  | NotExPartial (e1, s, n) -> "NotEx-Partial", [e1]
  | Refl (s, e1, e2) -> "Refl("^s^")", [e1; e2]
  | Trans (e1, e2) -> "Trans", [e1; e2]
  | Trans_sym (e1, e2) -> "Trans-sym", [e1; e2]
  | TransEq (e1, e2, e3) -> "TransEq", [e1; e2; e3]
  | TransEq2 (e1, e2, e3) -> "TransEq2", [e1; e2; e3]
  | TransEq_sym (e1, e2, e3) -> "TransEq-sym", [e1; e2; e3]
  | Cut (e1) -> "Cut", [e1]
  | CongruenceLR (p, a, b) -> "CongruenceLR", [p; a; b]
  | CongruenceRL (p, a, b) -> "CongruenceRL", [p; a; b]
  | Miniscope (e1, t, vs) -> "Miniscope", e1 :: t :: vs
  | Ext (th, ru, args) -> "Extension/"^th^"/"^ru, args
;;

let mlproof_rule o r =
  let rname, args = get_rule_name r in
  oprintf o "%s" rname;
  List.iter (fun e -> oprintf o ", "; expr o e) args;
  flush ();
;;

let mlproof_rule_soft o r =
  let rname, args = get_rule_name r in
  oprintf o "%s" rname;
  let f e =
    oprintf o ", [%d]" (Index.get_number e);
    expr_soft o e;
  in
  List.iter f args;
  flush ();
;;

let mlrule_short o r =
  let rname, args = get_rule_name r in
  oprintf o "%s" rname;
;;

let cur_step = ref 0;;
let new_step () = incr cur_step; !cur_step;;

let rec mlproof_aux o p =
  if p.mlrefc < 1 then
    - p.mlrefc
  else begin
    let subs = Array.map (mlproof_aux o) p.mlhyps in
    let n = new_step () in
    oprintf o "%d. " n;
    sequent o p.mlconc;
    oprintf o "  ### ";
    mlrule_short o p.mlrule;
    Array.iter (fun x -> oprintf o " %d" x) subs;
    oprintf o "\n";
    p.mlrefc <- -n;
    n
  end
;;

let mlproof o p =
  ignore (mlproof_aux o p);
  flush ();
;;

let hlrule_name = function
  | Close (e) -> "Axiom", [e; enot (e)]
  | Close_refl (s, e) -> "Refl("^s^")", [enot (eapp (s, [e; e]))]
  | Close_sym (s, e1, e2) ->
      "Sym("^s^")", [eapp (s, [e1; e2]); enot (eapp (s, [e2; e1]))]
  | False -> "False", []
  | NotTrue -> "NotTrue", []
  | NotNot (e) -> "NotNot", [enot (enot (e))]
  | And (e1, e2) -> "And", [eand (e1, e2)]
  | NotOr (e1, e2) -> "NotOr", [enot (eor (e1, e2))]
  | NotImpl (e1, e2) -> "NotImply", [enot (eimply (e1, e2))]
  | NotAll (e) -> "NotAll", [e]
  | NotAllEx (e) -> "NotAllEx", [e]
  | Ex (e) -> "Exists", [e]
  | All (e1, e2) -> "All", [e1]
  | NotEx (e1, e2) -> "NotExists", [e1]
  | Or (e1, e2) -> "Or", [eor (e1, e2)]
  | Impl (e1, e2) -> "Imply", [eimply (e1, e2)]
  | NotAnd (e1, e2) -> "NotAnd", [enot (eand (e1, e2))]
  | Equiv (e1, e2) -> "Equiv", [eequiv (e1, e2)]
  | NotEquiv (e1, e2) -> "NotEquiv", [enot (eequiv (e1, e2))]
  | P_NotP (e1, e2) -> "P-NotP", [e1; e2]
  | P_NotP_sym (s, e1, e2) -> "P-NotP-sym("^s^")", [e1; e2]
  | NotEqual (e1, e2) -> "NotEqual", [enot (eapp ("=", [e1; e2]))]
  | Definition (DefReal (_, s, _, _, _), e, _)
  | Definition (DefPseudo (_, s, _, _), e, _)
  | Definition (DefRec (_, s, _, _), e, _)
  -> "Definition("^s^")", [e]
  | ConjTree (e) -> "ConjTree", [e]
  | DisjTree (e) -> "DisjTree", [e]
  | AllPartial (e1, s, n) -> "All", [e1]
  | NotExPartial (e1, s, n) -> "NotExists", [e1]
  | Refl (s, e1, e2) -> "Refl("^s^")", [enot (eapp (s, [e1; e2]))]
  | Trans (e1, e2) -> "Trans", [e1; e2]
  | Trans_sym (e1, e2) -> "Trans-sym", [e1; e2]
  | TransEq (e1, e2, e3) -> "TransEq", [e1; e2; e3]
  | TransEq2 (e1, e2, e3) -> "TransEq2", [e1; e2; e3]
  | TransEq_sym (e1, e2, e3) -> "TransEq-sym", [e1; e2; e3]
  | Cut (e1) -> "Cut", [e1]
  | CongruenceLR (p, a, b) -> "CongruenceLR", [p; a; b]
  | CongruenceRL (p, a, b) -> "CongruenceRL", [p; a; b]
  | Miniscope (e1, t, vs) -> "Miniscope", e1 :: t :: vs
  | Ext (th, ru, args) -> ("Extension/"^th^"/"^ru), args
;;

let hlrule o r =
  let rname, args = hlrule_name r in
  oprintf o "[%s" rname;
  List.iter (fun x -> oprintf o " H%d" (Index.get_number x)) args;
  oprintf o "]";
;;

let rec vertical_sequent o ctx fms =
  match fms with
  | [] -> ()
  | h :: t ->
      if List.exists (Expr.equal h) ctx
      then vertical_sequent o ctx t
      else begin
        oprintf o "H%d: " (Index.get_number h);
        expr_soft o h;
        oprintf o "\n      ";
        vertical_sequent o ctx t;
      end;
;;


let rec hlproof o chaining depth ctx n p =
  let pr f = oprintf o f in
  if p.mlrefc < 1 then begin
    if (not chaining) then pr "\n";
    pr "%4d. see %d\n" n (- p.mlrefc);
  end else if depth >= 0 then begin
    match p.mlrule with
    | And _ | NotOr _ | NotImpl _ | NotAll _ | Ex _ | ConjTree _
    | AllPartial _ | NotExPartial _ | Definition _ ->
        assert (Array.length p.mlhyps = 1);
        hlproof o chaining depth ctx n p.mlhyps.(0)
    | _ ->
        if (not chaining) then pr "\n";
        pr "%4d. " n;
        vertical_sequent o ctx p.mlconc;
        let subs = Array.map (fun _ -> new_step ()) p.mlhyps in
        pr "### ";
        if depth = 0 && subs <> [| |] then begin
          pr "...proof-omitted...\n";
          Array.iter (hlproof o true (depth-1) ctx n) p.mlhyps;
        end else begin
          hlrule o p.mlrule;
          if subs <> [| |] then pr " -->";
          Array.iter (fun x -> pr " %d" x) subs;
          pr "\n";
          for i = 0 to Array.length p.mlhyps - 1 do
            hlproof o (i = 0) (depth-1) p.mlconc subs.(i) p.mlhyps.(i);
          done;
        end;
        p.mlrefc <- -n;
  end
;;

let hlproof o depth p =
  ignore (hlproof o true depth [] (new_step ()) p);
  flush ();
;;

open Llproof;;

let indent o i = for j = 0 to i do oprintf o "  "; done;;

let rec llproof_expr o e =
  let pro f = oprintf o f in
  match e with
  | Efalse -> pro "false";
  | Etrue -> pro "true";
  | Enot (p, _) -> pro "~"; llproof_expr o p;
  | Eand (p1, p2, _) ->
      pro "(";
      llproof_expr o p1;
      pro " /\\ ";
      llproof_expr o p2;
      pro ")";
  | Eor (p1, p2, _) ->
      pro "(";
      llproof_expr o p1;
      pro " \\/ ";
      llproof_expr o p2;
      pro ")";
  | Eimply (p1, p2, _) ->
      pro "(";
      llproof_expr o p1;
      pro " => ";
      llproof_expr o p2;
      pro ")";
  | Eequiv (p1, p2, _) ->
      pro "(";
      llproof_expr o p1;
      pro " <=> ";
      llproof_expr o p2;
      pro ")";
  | Eall (v, t, p, _) ->
      pro "All %a, " print_vartype (v, t); llproof_expr o p;
  | Eex (v, t, p, _) ->
      pro "Ex %a, " print_vartype (v, t); llproof_expr o p;
  | Elam (v, t, p, _) ->
      pro "(lambda %a, " print_vartype (v, t); llproof_expr o p; pro ")";
  | Etau (v, t, p, _) ->
      pro "(tau %a, " print_vartype (v, t); llproof_expr o p; pro ")";
  | Eapp (s, [e1; e2], _) when is_infix_op s ->
     pro "("; llproof_expr o e1; pro " %s " s; llproof_expr o e2; pro ")";
  | Eapp (s, [], _) -> pro "%s" s;
  | Eapp (s, args, _) -> pro "%s(" s; llproof_expr_list o args; pro ")";
  | Evar (s, _) -> pro "%s" s;
  | Emeta _
    -> assert false;

and llproof_expr_list o l =
  match l with
  | [] -> ()
  | [t] -> llproof_expr o t;
  | t::ts -> llproof_expr o t; oprintf o ", "; llproof_expr_list o ts;
;;

let binop_name = function
  | And -> "And"
  | Or -> "Or"
  | Imply -> "Imply"
  | Equiv -> "Equiv"
;;

let llproof_rule o r =
  let pr f = oprintf o f in
  match r with
  | Rfalse -> pr "---false";
  | Rnottrue -> pr "---nottrue";
  | Raxiom (p) -> pr "---axiom "; llproof_expr o p;
  | Rcut (p) -> pr "---cut "; llproof_expr o p;
  | Rnoteq (t) -> pr "---noteq "; llproof_expr o t;
  | Reqsym (t, u) ->
     pr "---eqsym (";
     llproof_expr o t;
     pr ", ";
     llproof_expr o u;
     pr ")";
  | Rnotnot (p) -> pr "---notnot "; llproof_expr o p;
  | Rconnect (op, p, q) ->
      pr "---connect (%s, " (binop_name op);
      llproof_expr o p;
      pr ", ";
      llproof_expr o q;
      pr ")";
  | Rnotconnect (op, p, q) ->
      pr "---notconnect (%s, " (binop_name op);
      llproof_expr o p;
      pr ", ";
      llproof_expr o q;
      pr ")";
  | Rex (p, e) ->
      pr "---ex (";
      llproof_expr o p;
      pr ", ";
      llproof_expr o e;
      pr ")";
  | Rall (p, t) ->
      pr "---all (";
      llproof_expr o p;
      pr ", ";
      llproof_expr o t;
      pr ")";
  | Rnotex (p, t) ->
      pr "---notex (";
      llproof_expr o p;
      pr ", ";
      llproof_expr o t;
      pr ")";
  | Rnotall (p, e) ->
      pr "---notall (";
      llproof_expr o p;
      pr ", ";
      llproof_expr o e;
      pr ")";
  | Rpnotp (p, q) ->
      pr "---pnotp (";
      llproof_expr o p;
      pr ", ";
      llproof_expr o q;
      pr ")";
  | Rnotequal (t, u) ->
      pr "---notequal (";
      llproof_expr o t;
      pr ", ";
      llproof_expr o u;
      pr ")";
  | RcongruenceLR (p, a, b) ->
      pr "---congruenceLR (";
      llproof_expr o p;
      pr ", ";
      llproof_expr o a;
      pr ", ";
      llproof_expr o b;
      pr ")";
  | RcongruenceRL (p, a, b) ->
      pr "---congruenceRL (";
      llproof_expr o p;
      pr ", ";
      llproof_expr o a;
      pr ", ";
      llproof_expr o b;
      pr ")";
  | Rdefinition (name, sym, args, body, decarg, folded, unfolded) ->
      pr "---definition \"%s\" (%s)" name sym;
  | Rextension (ext, name, args, c, hyps) ->
      pr "---extension (%s/%s" ext name;
      List.iter (fun x -> pr " "; llproof_expr o x) args;
      pr ")";
  | Rlemma (name, args) ->
      pr "---lemma %s [ " name;
      List.iter (fun x -> llproof_expr o x; pr " ") args;
      pr "]";
;;

let nodes = ref 0;;

let rec llproof_tree o i t =
  let pr = oprintf o in
  let prop_space p = llproof_expr o p; pr "   "; in
  indent o i; List.iter prop_space t.conc; pr "\n";
  indent o i; llproof_rule o t.rule; pr "\n";
  List.iter (llproof_tree o (i+1)) t.hyps;
  incr nodes;
;;

let print_idtype o (ty, act) =
  if ty = univ_name
  then begin
    llproof_expr o act;
    oprintf o " ";
  end else begin
    oprintf o "(";
    llproof_expr o act;
    oprintf o "):\"%s\" " ty
  end
;;

let llproof_lemma o {name=name; params=params; proof=tree} =
  let pr f = oprintf o f in
  pr "%s" name;
  if params <> [] then begin
    pr " [";
    List.iter (print_idtype o) params;
    pr "]";
  end;
  pr "\n";
  llproof_tree o 1 tree;
  pr "\n";
;;

let llproof o p =
  List.iter (llproof_lemma o) p;
  flush ();
;;
