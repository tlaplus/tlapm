(*  Copyright 2008 INRIA  *)

open Printf;;

open Expr;;
open Llproof;;
open Misc;;
open Namespace;;

module Dict = Set.Make (String);;

let rec dict_addlist l d =
  match l with
  | [] -> d
  | h::t -> dict_addlist t (Dict.add h d)
;;

let dict_add x d = Dict.add x d;;
let dict_mem x d = Dict.mem x d;;
let dict_empty = Dict.empty;;

module Int = struct
  type t = int;;
  let compare = Stdlib.compare;;
end;;
module Hypdict = Map.Make (Int);;

let iprintf i oc fmt (* args *) =
  fprintf oc "%s" (String.make i ' ');
  fprintf oc fmt (* args *);
;;

let iinc i = if i >= 15 then i else i+1;;

let vname e = "?z_h" ^ (base26 (Index.get_number e));;
let hname hyps e =
  let n = Index.get_number e in
  try Hypdict.find n hyps
  with Not_found -> "z_H" ^ (base26 n)
;;

let apply lam arg =
  match lam with
  | Elam (v, t, e1, _) -> substitute [(v, arg)] e1
  | _ -> assert false
;;

let rec p_list dict init printer sep oc l =
  match l with
  | [] -> ()
  | [x] -> fprintf oc "%s%a" init (printer dict) x;
  | h::t ->
      fprintf oc "%s%a%s" init (printer dict) h sep;
      p_list dict init printer sep oc t;
;;

let tr_infix s =
  match s with
  | "=" -> "="
  | "TLA.cup" -> " \\\\cup "
  | "TLA.cap" -> " \\\\cap "
  | "TLA.setminus" -> " \\\\ "
  | "TLA.in" -> " \\\\in "
  | "TLA.subseteq" -> " \\\\subseteq "
  | "arith.natrange" -> ".."  (* see also arith.intrange below *)
  | "arith.add" -> " + "
  | "arith.sub" -> " - "
  | "arith.mul" -> " * "
(*  | "arith.power" -> " ^ " not defined yet *)
  | "arith.le" -> " <= "
  | "arith.lt" -> " < "
  | "TLA.concat" -> " \\\\circ "
  | "TLA.oneArg" -> " :> "
  | "TLA.extend" -> " @@ "
  | _ -> "" (* see is_infix below *)
;;

let is_infix s = tr_infix s <> "";;

let tr_constant s =
  match s with
  | "TLA.emptyset" -> "{}"
  | "arith.N" -> "Nat"
  | "arith.Z" -> "Int"
  | "arith.R" -> "isReal"             (* FIXME will change *)
  | "arith.Infinity" -> "isInfinity"  (* FIXME will change *)
  | _ when String.length s > 4 && String.sub s 0 4 = "TLA." ->
     String.sub s 4 (String.length s - 4)
  | _ when String.length s > 6 && String.sub s 0 6 = "arith." ->
     String.sub s 6 (String.length s - 6)
  | _ -> s
;;

let tr_prefix s =
  match s with
  | "arith.div" -> "isa'slash"       (* FIXME will change *)
  | "arith.euclidiv" -> "isa'div"    (* FIXME will change *)
  | "arith.mod" -> "isa'pc"          (* FIXME will change *)
  | "arith.minus" -> " -."
  | "arith.intrange" -> "isa'dotdot"  (* see arith.natrange above *)
  | "TLA.box" -> "isa'box"
  | _ when String.length s > 4 && String.sub s 0 4 = "TLA." ->
     String.sub s 4 (String.length s - 4)
  | _ when String.length s > 6 && String.sub s 0 6 = "arith." ->
     String.sub s 6 (String.length s - 6)
  | _ -> s
;;

let disjoint l1 l2 = not (List.exists (fun x -> List.mem x l1) l2);;

let rec is_nat x limit =
  match x with
  | _ when limit < 0 -> false
  | Evar ("0", _) -> true
  | Eapp ("TLA.fapply", [Evar ("TLA.Succ", _); y], _) -> is_nat y (limit - 1)
  | _ -> false
;;

let rec get_nat x =
  match x with
  | Evar ("0", _) -> 0
  | Eapp ("TLA.fapply", [Evar ("TLA.Succ", _); y], _) -> 1 + get_nat y
  | _ -> assert false
;;

let rec make_pairs l =
  match l with
  | a :: b :: t -> (a, b) :: make_pairs t
  | _ -> []
;;

let rec p_expr env dict oc e =
  let poc fmt = fprintf oc fmt in
  match e with
  | _ when dict_mem (vname e) dict && disjoint env (get_fv e) ->
      poc "%s" (vname e)
  | Evar (v, _) when Mltoll.is_meta v ->
      poc "(CHOOSE x : TRUE)";
  | Evar (v, _) ->
      poc "%s" (tr_constant v);
  | Eapp ("$string", [Evar (s, _)], _) when String.length s >= 2 ->
      poc "''%s''" (String.sub s 1 (String.length s - 2))
  | Eapp ("$string", _, _) -> assert false
  | Eapp ("TLA.set", l, _) ->
      poc "{%a}" (p_expr_list env dict) l;
  | Eapp ("TLA.tuple", l, _) ->
      poc "<<%a>>" (p_expr_list env dict) l;
  | Eapp ("TLA.record", l, _) ->
      poc "(%a)" (p_list dict "" (p_record_field env) " @@ ") (make_pairs l)
  | Eapp ("TLA.recordset", l, _) ->
      poc "[%a]" (p_list dict "" (p_recordset_field env) ", ") (make_pairs l)
  | Eapp ("TLA.CASE", l, _) ->
      poc "(CASE %a)" (p_case_arms env dict) l;
  | Eapp ("TLA.fapply", [Evar ("TLA.Succ", _); x], _) when is_nat x 14 ->
      poc "%d" (get_nat e)
  | Eapp ("TLA.fapply", [f; x], _) ->
      poc "(%a[%a])" (p_expr env dict) f (p_expr env dict) x
  | Eapp (f, [e1; e2], _) when is_infix f ->
      poc "(%a%s%a)" (p_expr env dict) e1 (tr_infix f) (p_expr env dict) e2;
  | Eapp (f, [], _) -> poc "%s" f;
  | Eapp (f, l, _) ->
      poc "%s(%a)" (tr_prefix f) (p_expr_list env dict) l;
  | Enot (Eapp ("=", [e1; e2], _), _) ->
      poc "(%a~=%a)" (p_expr env dict) e1 (p_expr env dict) e2;
  | Enot (e1, _) ->
      poc "(~%a)" (p_expr env dict) e1;
  | Eand (e1, e2, _) ->
      poc "(%a&%a)" (p_expr env dict) e1 (p_expr env dict) e2;
  | Eor (e1, e2, _) ->
      poc "(%a|%a)" (p_expr env dict) e1 (p_expr env dict) e2;
  | Eimply (e1, e2, _) ->
      poc "(%a=>%a)" (p_expr env dict) e1 (p_expr env dict) e2;
  | Eequiv (e1, e2, _) ->
      poc "(%a<=>%a)" (p_expr env dict) e1 (p_expr env dict) e2;
  | Etrue ->
      poc "TRUE";
  | Efalse ->
      poc "FALSE";
  | Eall (Evar (x, _), _, e, _) ->
      poc "(\\\\A %s:%a)" x (p_expr (x::env) dict) e;
  | Eall _ -> assert false
  | Eex (Evar (x, _), _, e, _) ->
      poc "(\\\\E %s:%a)" x (p_expr (x::env) dict) e;
  | Eex _ -> assert false
  | Elam (Evar (x, _), _, e, _) ->
      poc "(\\<lambda>%s. %a)" x (p_expr (x::env) dict) e;
  | Elam _ -> assert false
  | Etau (Evar (x, _), _, e, _) ->
      poc "(CHOOSE %s:%a)" x (p_expr (x::env) dict) e;
  | Etau _ -> assert false
  | Emeta _ -> assert false

and p_expr_list env dict oc l = p_list dict "" (p_expr env) ", " oc l;

and p_case_arms env dict oc l =
  match l with
  | [] -> assert false
  | [e] -> fprintf oc "OTHER -> %a" (p_expr env dict) e
  | [c; e] ->
     fprintf oc "%a -> %a" (p_expr env dict) c (p_expr env dict) e;
  | c :: e :: t ->
     fprintf oc "%a -> %a [] " (p_expr env dict) c (p_expr env dict) e;
     p_case_arms env dict oc t;

and p_record_field env dict oc (l, e) =
  fprintf oc "%a :> (%a)" (p_expr env dict) l (p_expr env dict) e

and p_recordset_field env dict oc (l, e) =
  fprintf oc "%a : (%a)" (p_expr env dict) l (p_expr env dict) e
;;

let p_expr dict oc e = p_expr [] dict oc e;;
let p_expr_list dict oc l = p_expr_list [] dict oc l;;

let p_apply dict oc (lam, arg) =
  let n_lam = vname lam in
  if dict_mem n_lam dict then
    fprintf oc "%s(%a)" n_lam (p_expr dict) arg
  else
    p_expr dict oc (apply lam arg)
;;

let mk_pat dict e =
  match e with
  | Evar (v, _) when not (Mltoll.is_meta v) -> ("_", dict)
  | _ ->
     let n = vname e in
     if dict_mem n dict then ("_", dict) else (n, dict_add n dict)
;;

let rec mk_pairs l =
  match l with
  | [] -> []
  | a :: b :: t -> (a, b) :: (mk_pairs t)
  | _ -> Error.warn "record or record set with odd number of fields"; []
;;

let p_is dict oc h =
  let binary pre e1 op e2 post =
    let (p1, dict1) = mk_pat dict e1 in
    let (p2, dict2) = mk_pat dict1 e2 in
    if p1 = "_" && p2 = "_"
    then fprintf oc "\n"
    else fprintf oc " (is \"%s%s%s%s%s\")\n" pre p1 op p2 post;
    dict2
  in
  let unary pre e post =
    let (p, dict1) = mk_pat dict e in
    if p = "_"
    then fprintf oc "\n"
    else fprintf oc " (is \"%s%s%s\")\n" pre p post;
    dict1
  in
  match h with
  | Eand (e1, e2, _) -> binary "" e1 "&" e2 ""
  | Eor (e1, e2, _) -> binary "" e1 "|" e2 ""
  | Eimply (e1, e2, _) -> binary "" e1 "=>" e2 ""
  | Eequiv (e1, e2, _) -> binary "" e1 "<=>" e2 ""
  | Enot (Eand (e1, e2, _), _) -> binary "~(" e1 "&" e2 ")"
  | Enot (Eor (e1, e2, _), _) -> binary "~(" e1 "|" e2 ")"
  | Enot (Eimply (e1, e2, _), _) -> binary "~(" e1 "=>" e2 ")"
  | Enot (Eequiv (e1, e2, _), _) -> binary "~(" e1 "<=>" e2 ")"
  | Eall (v, t, e1, _) -> unary "\\\\A x : " (elam (v, t, e1)) "(x)"
  | Eex (v, t, e1, _) -> unary "\\\\E x : " (elam (v, t, e1)) "(x)"
  | Enot (Eall (v, t, e1, _), _) -> unary "~(\\\\A x : " (elam (v, t, e1)) "(x))"
  | Enot (Eex (v, t, e1, _), _) -> unary "~(\\\\E x : " (elam (v, t, e1)) "(x))"
  | Enot (Enot (e1, _), _) -> unary "~~" e1 ""
  | Eapp ("=", [e1; e2], _) -> binary "" e1 "=" e2 ""
  | Enot (Eapp ("=", [e1; e2], _), _) -> binary "" e1 "~=" e2 ""
  | Enot (e1, _) -> unary "~" e1 ""
  | _ -> unary "" h ""
;;

let p_let dict i oc e =
  let (p, dict1) = mk_pat dict e in
  if p <> "_" then iprintf i oc "let %s = \"%a\"\n" p (p_expr dict) e;
  dict1
;;

let p_assume hyps i dict oc h =
  iprintf i oc "assume %s:\"%a\"" (hname hyps h) (p_expr dict) h;
  p_is dict oc h
;;

let p_sequent hyps i dict oc hs =
  List.fold_left (fun dict h -> p_assume hyps i dict oc h) dict hs
;;

let tla_succ n = eapp ("TLA.fapply", [evar "TLA.Succ"; n]);;
let tla_zero = evar "0";;
let tla_one = tla_succ tla_zero;;

let rec p_tree hyps i dict oc proof =
  let alpha = p_alpha hyps i dict oc in
  let beta = p_beta hyps i dict oc in
  let gamma = p_gamma hyps i dict oc in
  let delta = p_delta hyps i dict oc in
  match proof.rule with
  | Rconnect (And, e1, e2) ->
     alpha "and" (eand (e1, e2)) [e1; e2] proof.hyps;
  | Rconnect (Or, e1, e2) ->
     beta "or" (eor (e1, e2)) [[e1]; [e2]] proof.hyps;
  | Rconnect (Imply, e1, e2) ->
     beta "imply" (eimply (e1, e2)) [[enot (e1)]; [e2]] proof.hyps;
  | Rconnect (Equiv, e1, e2) ->
     beta "equiv" (eequiv (e1, e2)) [[enot (e1); enot (e2)]; [e1; e2]]
          proof.hyps;
  | Rnotconnect (And, e1, e2) ->
     beta "notand" (enot (eand (e1, e2))) [[enot (e1)]; [enot (e2)]] proof.hyps;
  | Rnotconnect (Or, e1, e2) ->
     alpha "notor" (enot (eor (e1, e2))) [enot (e1); enot (e2)] proof.hyps;
  | Rnotconnect (Imply, e1, e2) ->
     alpha "notimply" (enot (eimply (e1, e2))) [e1; enot (e2)] proof.hyps;
  | Rnotconnect (Equiv, e1, e2) ->
     beta "notequiv" (enot (eequiv (e1, e2)))
          [[enot (e1); e2]; [e1; enot (e2)]] proof.hyps;
  | Rextension (_, "zenon_case", [p], [con], hs) ->
     let arity = List.length hs - 1 in
     let other =
       let rec loop l =
         match l with
         | [ [x] ] -> false
         | [ [x; y] ] -> true
         | h :: t -> loop t
         | _ -> assert false
       in loop hs
     in
     iprintf i oc "show FALSE\n";
     iprintf i oc "proof (rule zenon_case%s%d [of \"%a\", OF %s])\n"
                  (if other then "other" else "") arity
                  (p_expr dict) p (hname hyps con);
     let rec p_sub dict l1 l2 =
       match l1, l2 with
       | h::hs, t::ts ->
          let dict2 = p_sequent hyps (iinc i) dict oc h in
          p_tree hyps (iinc i) dict2 oc t;
          iprintf i oc "%s\n" (if hs = [] then "qed" else "next");
          p_sub dict hs ts;
       | [], [] -> ()
       | _ -> assert false
     in
     p_sub dict hs proof.hyps;
  | Rextension (_, "zenon_case", _, _, _) -> assert false

  | Rextension (_, "zenon_stringequal", [v1; v2], [con], []) ->
     let v1nev2 = enot (con) in
     iprintf i oc "have %s: \"%a\"\n" (hname hyps v1nev2) (p_expr dict) v1nev2;
     iprintf i oc "by (simp only: zenon_sa_1 zenon_sa_2,\n";
     iprintf i oc "    ((rule zenon_sa_diff_2)+)?,\n";
     iprintf i oc "    (rule zenon_sa_diff_3, auto)?,\n";
     iprintf i oc "    (rule zenon_sa_diff_1, auto)?,\n";
     iprintf i oc "    (rule zenon_sa_diff_0a)?, (rule zenon_sa_diff_0b)?)\n";
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule notE [OF %s %s])\n" (hname hyps v1nev2)
             (hname hyps con);
  | Rextension (_, "zenon_stringequal", _, _, _) -> assert false
  | Rextension (_, "zenon_stringdiffll", [e1; s1; e2; s2], [c1; c2], [[h]]) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let s1nes2 = enot (eapp ("=", [s1; s2])) in
     iprintf i oc "have %s: \"%a\"\n" (hname hyps s1nes2) (p_expr dict) s1nes2;
     iprintf i oc "by auto\n";
     iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict) h;
     let dict1 = p_is dict oc h in
     iprintf i oc "by (rule zenon_stringdiffll [OF %s %s %s])\n"
             (hname hyps s1nes2) (hname hyps c1) (hname hyps c2);
     p_tree hyps (iinc i) dict1 oc t
  | Rextension (_, "zenon_stringdiffll", _, _, _) -> assert false
  | Rextension (_, "zenon_stringdifflr", [e1; s1; e2; s2], [c1; c2], [[h]]) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let s1nes2 = enot (eapp ("=", [s1; s2])) in
     iprintf i oc "have %s: \"%a\"\n" (hname hyps s1nes2) (p_expr dict) s1nes2;
     iprintf i oc "by auto\n";
     iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict) h;
     let dict1 = p_is dict oc h in
     iprintf i oc "by (rule zenon_stringdifflr [OF %s %s %s])\n"
             (hname hyps s1nes2) (hname hyps c1) (hname hyps c2);
     p_tree hyps (iinc i) dict1 oc t
  | Rextension (_, "zenon_stringdifflr", _, _, _) -> assert false
  | Rextension (_, "zenon_stringdiffrl", [e1; s1; e2; s2], [c1; c2], [[h]]) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let s1nes2 = enot (eapp ("=", [s1; s2])) in
     iprintf i oc "have %s: \"%a\"\n" (hname hyps s1nes2) (p_expr dict) s1nes2;
     iprintf i oc "by auto\n";
     iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict) h;
     let dict1 = p_is dict oc h in
     iprintf i oc "by (rule zenon_stringdiffrl [OF %s %s %s])\n"
             (hname hyps s1nes2) (hname hyps c1) (hname hyps c2);
     p_tree hyps (iinc i) dict1 oc t
  | Rextension (_, "zenon_stringdiffrl", _, _, _) -> assert false
  | Rextension (_, "zenon_stringdiffrr", [e1; s1; e2; s2], [c1; c2], [[h]]) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let s1nes2 = enot (eapp ("=", [s1; s2])) in
     iprintf i oc "have %s: \"%a\"\n" (hname hyps s1nes2) (p_expr dict) s1nes2;
     iprintf i oc "by auto\n";
     iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict) h;
     let dict1 = p_is dict oc h in
     iprintf i oc "by (rule zenon_stringdiffrr [OF %s %s %s])\n"
             (hname hyps s1nes2) (hname hyps c1) (hname hyps c2);
     p_tree hyps (iinc i) dict1 oc t
  | Rextension (_, "zenon_stringdiffrr", _, _, _) -> assert false

  | Rextension (_, "zenon_tuple_eq_match", [], [c], [hs]) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let p_hyp dict h =
       if List.memq h t.conc then begin
         iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict) h;
         let dict2 = p_is dict oc h in
         iprintf i oc "using %s by auto\n" (hname hyps c);
         dict2
       end else dict
     in
     let dict3 = List.fold_left p_hyp dict hs in
     p_tree hyps i dict3 oc t
  | Rextension (_, "zenon_tuple_eq_match", _, _, _) -> assert false
  | Rextension (_, "zenon_tuple_eq_mismatch", [e], [c], []) ->
     iprintf i oc "show FALSE\n";
     iprintf i oc "using %s by auto\n" (hname hyps e);
  | Rextension (_, "zenon_tuple_eq_mismatch", _, _, _) -> assert false
  | Rextension (_, ("zenon_tuple_access"|"zenon_tuple_len"
                    |"zenon_record_domain"),
                [p; olde; newe], [c], [[h]]) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let eqn = eapp ("=", [olde; newe]) in
     iprintf i oc "have %s: \"%a\"" (hname hyps eqn) (p_expr dict) eqn;
     let dict2 = p_is dict oc eqn in
     iprintf i oc "by auto\n";
     iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict2) h;
     let dict3 = p_is dict2 oc h in
     iprintf i oc "by (rule subst [where P=\"%a\", OF %s %s])\n"
             (p_expr dict) p (hname hyps eqn) (hname hyps c);
     p_tree hyps i dict3 oc t
  | Rextension (_, ("zenon_tuple_access"|"zenon_tuple_len"
                    |"zenon_record_domain"), _, _, _) ->
     assert false
  | Rextension (_, "zenon_record_access", [p; olde; newe], [c], [[h]]) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let (r, fld, idx, len) =
       match olde with
       | Eapp ("TLA.fapply", [Eapp ("TLA.record", l, _) as r; field], _) ->
          r, field, (Misc.list_indexq field l) / 2 + 1, (List.length l) / 2
       | _ -> assert false
     in
     let indom = eapp ("TLA.in", [fld; eapp ("TLA.DOMAIN", [r])]) in
     let eqn = eapp ("=", [olde; newe]) in
     let eqx = eand (indom, eqn) in
     iprintf i oc "have %s: \"%a\"" (hname hyps eqx) (p_expr dict) eqx;
     let dict = p_is dict oc eqx in
     if idx = 1 then begin
       iprintf i oc "by ((rule zenon_recfield_1)+, rule zenon_recfield_2b)\n"
     end else begin
       iprintf i oc "by (";
       for j = len downto idx + 1 do
         fprintf oc "rule zenon_recfield_1, ";
       done;
       fprintf oc "rule zenon_recfield_2, ((rule zenon_recfield_3)+)?, ";
       fprintf oc "rule zenon_recfield_3b, auto)\n";
     end;
     iprintf i oc "have %s: \"%a\"" (hname hyps eqn) (p_expr dict) eqn;
     let dict = p_is dict oc eqn in
     iprintf i oc "by (rule conjD2 [OF %s])\n" (hname hyps eqx);
     iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict) h;
     let dict = p_is dict oc h in
     iprintf i oc "by (rule subst [where P=\"%a\", OF %s %s])\n"
             (p_expr dict) p (hname hyps eqn) (hname hyps c);
     p_tree hyps i dict oc t
  | Rextension (_, "zenon_record_access", _, _, _) ->
     assert false
  | Rextension (_, "zenon_in_product", [e1; e2], [c], [h0 :: h1 :: hs]) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let dict1 = p_let dict i oc e1 in
     let dict2 = p_let dict1 i oc e2 in
     let p_simple_hyp h =
       if List.memq h t.conc then
         iprintf i oc "have %s: \"%a\" using %s by auto\n"
                 (hname hyps h) (p_expr dict2) h (hname hyps c)
     in
     p_simple_hyp h0;
     p_simple_hyp h1;
     let isseq = eapp ("TLA.isASeq", [e2]) in
     iprintf i oc "have %s: \"%a\" by auto\n"
             (hname hyps isseq) (p_expr dict2) isseq;
     let print_hyp (dict2, n) h =
       if List.memq h t.conc then begin
         let inlen =
           eapp ("TLA.in", [n; eapp ("arith.natrange",
                                     [tla_one; eapp ("TLA.Len", [e2])])])
         in
         iprintf i oc "have %s: \"%a\" by auto\n"
                 (hname hyps inlen) (p_expr dict2) inlen;
         let hh = eapp ("TLA.in", [eapp ("TLA.fapply", [e1; n]);
                                   eapp ("TLA.fapply", [e2; n])])
         in
         iprintf i oc "have %s: \"%a\"" (hname hyps hh) (p_expr dict2) hh;
         let dict3 = p_is dict2 oc hh in
         iprintf i oc "by (rule zenon_in_product_i [OF %s %s %s])\n"
                 (hname hyps c) (hname hyps isseq) (hname hyps inlen);
         iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict3) h;
         let dict4 = p_is dict3 oc h in
         iprintf i oc "using %s by auto\n" (hname hyps hh);
         (dict4, tla_succ n)
       end else (dict2, tla_succ n)
     in
     let (dict4, _) = List.fold_left print_hyp (dict2, tla_one) hs in
     p_tree hyps i dict4 oc t
  | Rextension (_, "zenon_in_product", _, _, _) -> assert false
  | Rextension (_, "zenon_notin_product", [e1; e2], [c], hs) ->
     let dict1 = p_let dict i oc e1 in
     let print_hyp dict1 nhl t =
       let h, nh =
         match nhl with
         | [Enot (h, _) as nh] -> h, nh
         | _ -> assert false
       in
       iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict1) h;
       let dict2 = p_is dict1 oc h in
       iprintf i oc "proof (rule zenon_nnpp)\n";
       iprintf (i+1) oc "assume %s: \"%a\"" (hname hyps nh) (p_expr dict2) nh;
       let dict3 = p_is dict2 oc nh in
       p_tree hyps (i+1) dict3 oc t;
       iprintf i oc "qed\n";
       dict2
     in
     let dict2 = List.fold_left2 print_hyp dict1 hs proof.hyps in
     iprintf i oc "show FALSE using %s " (hname hyps c);
     let print_hyp_name oc nhl =
       let h = match nhl with [Enot (h, _)] -> h | _ -> assert false in
       fprintf oc "%s " (hname hyps h);
     in
     List.iter (print_hyp_name oc) hs;
     fprintf oc "inProductI[where s=\"%a\"] " (p_expr dict2) e2;
     fprintf oc "by auto\n";
  | Rextension (_, "zenon_notin_product", _, _, _) -> assert false
  | Rextension (_, "zenon_tuple_notisaseq", [], [c], []) ->
     iprintf i oc "show FALSE using %s by auto\n" (hname hyps c);
  | Rextension (_, "zenon_tuple_notisaseq", _, _, _) -> assert false

  | Rextension (_, "zenon_record_eq_match", [], [c], [hs]) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let p_hyp dict h =
       if List.memq h t.conc then begin
         iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict) h;
         let dict2 = p_is dict oc h in
         iprintf i oc "using %s by auto\n" (hname hyps c);
         dict2
       end else dict
     in
     let dict3 = List.fold_left p_hyp dict hs in
     p_tree hyps i dict3 oc t
  | Rextension (_, "zenon_record_eq_match", _, _, _) -> assert false
  | Rextension (_, "zenon_record_eq_mismatch", [e], [c], []) ->
     iprintf i oc "show FALSE\n";
     iprintf i oc "using %s by auto\n" (hname hyps e);
  | Rextension (_, "zenon_record_eq_mismatch", _, _, _) -> assert false
  | Rextension (_, "zenon_record_neq_match", _, _, _) ->
     iprintf i oc "sorry\n" (* FIXME TODO *)
  | Rextension (_, "zenon_neq_record", [e1; e2], [c], h0 :: h1 :: hs) ->
     iprintf i oc "sorry\n" (* FIXME TODO *)
  | Rextension (_, "zenon_neq_record", _, _, _) -> assert false
  | Rextension (_, "zenon_record_neq", [e1; e2], [c], h0 :: h1 :: hs) ->
     iprintf i oc "sorry\n" (* FIXME TODO *)
  | Rextension (_, "zenon_record_neq", _, _, _) -> assert false

  | Rextension (_, "zenon_in_recordset", [e1; e2], [c], [h0 :: h1 :: hs]) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let dict2 = p_let dict i oc e1 in
     let p_simple_hyp h =
       if List.memq h t.conc then
         iprintf i oc "have %s: \"%a\" using %s by auto\n"
                 (hname hyps h) (p_expr dict2) h (hname hyps c)
     in
     p_simple_hyp h0;
     p_simple_hyp h1;
     let args =
       match e2 with Eapp ("TLA.recordset", args, _) -> args | _ -> assert false
     in
     let l_args = mk_pairs args in
     let doms = eapp ("TLA.tuple", List.map fst l_args) in
     let rngs = eapp ("TLA.tuple", List.map snd l_args) in
     let dict3 = p_let dict2 i oc doms in
     let dict4 = p_let dict3 i oc rngs in
     let print_hyp (dict4, n) h =
       if List.memq h t.conc then begin
         let indom = eapp ("TLA.in", [n; eapp ("TLA.DOMAIN", [doms])]) in
         iprintf i oc "have %s: \"%a\" by auto\n"
                 (hname hyps indom) (p_expr dict4) indom;
         let hh =
           eapp ("TLA.in",
                 [eapp ("TLA.fapply", [e1; eapp ("TLA.fapply", [doms; n])]);
                  eapp ("TLA.fapply", [rngs; n])])
         in
         iprintf i oc "have %s: \"%a\"" (hname hyps hh) (p_expr dict4) hh;
         let dict5 = p_is dict4 oc hh in
         iprintf i oc "by (rule zenon_in_recordset_field [OF %s %s])\n"
                 (hname hyps c) (hname hyps indom);
         iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict5) h;
         let dict6 = p_is dict5 oc h in
         iprintf i oc "using %s by auto\n" (hname hyps hh);
         (dict6, tla_succ n)
       end else (dict4, tla_succ n)
     in
     let (dict6, _) = List.fold_left print_hyp (dict4, tla_one) hs in
     p_tree hyps i dict6 oc t
  | Rextension (_, "zenon_in_recordset", _, _, _) -> assert false
  | Rextension (_, "zenon_notin_recordset", [e1; e2], [c], hs) ->
     let dict1 = p_let dict i oc e1 in
     let print_hyp dict1 nhl t =
       let h, nh =
         match nhl with
         | [Enot (h, _) as nh] -> h, nh
         | _ -> assert false
       in
       iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict1) h;
       let dict2 = p_is dict1 oc h in
       iprintf i oc "proof (rule zenon_nnpp)\n";
       iprintf (i+1) oc "assume %s: \"%a\"" (hname hyps nh) (p_expr dict2) nh;
       let dict3 = p_is dict2 oc nh in
       p_tree hyps (i+1) dict3 oc t;
       iprintf i oc "qed\n";
       dict2
     in
     let _ = List.fold_left2 print_hyp dict1 hs proof.hyps in
     iprintf i oc "show FALSE by (rule notE [OF %s],\n" (hname hyps c);
     iprintf i oc "               rule zenon_inrecordsetI%d [OF "
             (List.length hs - 2);
     let print_hyp_name oc nhl =
       let h = match nhl with [Enot (h, _)] -> h | _ -> assert false in
       fprintf oc "%s " (hname hyps h);
     in
     List.iter (print_hyp_name oc) hs;
     fprintf oc "])\n";
  | Rextension (_, "zenon_notin_recordset", _, _, _) -> assert false
  | Rextension (_, "zenon_record_notisafcn", [], [c], []) ->
     iprintf i oc "show FALSE using %s by auto\n" (hname hyps c);
  | Rextension (_, "zenon_record_notisafcn", _, _, _) -> assert false

  | Rextension (_, name, args, con, []) ->
     let p_arg dict oc e = fprintf oc "\"%a\"" (p_expr dict) e in
     let p_con dict oc e = fprintf oc "%s" (hname hyps e) in
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule %s [of %a, OF %a])\n" name
             (p_list dict "" p_arg " ") args (p_list dict "" p_con " ") con;
  | Rextension (_, name, args, con, [hs]) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let p_arg dict oc e = fprintf oc "\"%a\"" (p_expr dict) e in
     let p_con dict oc e = fprintf oc "%s" (hname hyps e) in
     let p_hyp (dict, j) h =
       if List.memq h t.conc then begin
         iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict) h;
         let dict2 = p_is dict oc h in
         iprintf i oc "by (rule %s_%d [of %a, OF %a])\n" name j
                 (p_list dict2 "" p_arg " ") args (p_list dict2 "" p_con " ")
                 con;
         (dict2, j+1)
       end else (dict, j+1)
     in
     let (dict3, _) = List.fold_left p_hyp (dict, 0) hs in
     p_tree hyps i dict3 oc t
  | Rextension (_, name, args, con, hs) ->
     let p_arg dict oc e = fprintf oc "\"%a\"" (p_expr dict) e in
     let p_con dict oc e = fprintf oc "%s" (hname hyps e) in
     iprintf i oc "show FALSE\n";
     iprintf i oc "proof (rule %s [of %a, OF %a])\n" name
             (p_list dict "" p_arg " ") args (p_list dict "" p_con " ") con;
     let rec p_sub dict l1 l2 =
       match l1, l2 with
       | h::hs, t::ts ->
          let dict2 = p_sequent hyps (iinc i) dict oc h in
          p_tree hyps (iinc i) dict2 oc t;
          iprintf i oc "%s\n" (if hs = [] then "qed" else "next");
          p_sub dict hs ts;
       | [], [] -> ()
       | _, _ -> assert false
     in
     p_sub dict hs proof.hyps;
  | Rnotnot (e1) ->
     alpha "notnot" (enot (enot e1)) [e1] proof.hyps;
  | Rex (Eex (x, t, e1, _) as conc, e2) ->
     delta "ex_choose" false (elam (x, t, e1)) e2 conc proof.hyps;
  | Rex _ -> assert false
  | Rnotall (Eall (x, t, e1, _) as nconc, e2) ->
     delta "notall_choose" true (elam (x, t, e1)) e2 (enot nconc) proof.hyps;
  | Rnotall _ -> assert false
  | Rall (Eall (x, t, e1, _) as conc, e2) ->
     gamma "all" false (elam (x, t, e1)) e2 conc proof.hyps;
  | Rall _ -> assert false
  | Rnotex (Eex (x, t, e1, _) as nconc, e2) ->
     gamma "notex" true (elam (x, t, e1)) e2 (enot nconc) proof.hyps;
  | Rnotex _ -> assert false
  | Rlemma (l, a) ->
     let rec filter_vars l =
      match l with
      | [] -> []
      | Evar (v, _) :: t -> v :: filter_vars t
      | Etau _ :: t -> filter_vars t
      | _ -> assert false
     in
     let pr dict oc v = fprintf oc "?%s=%s" v v in
     let pr_hyp dict oc h = fprintf oc "%s" (hname hyps h) in
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule %s [" l;
     begin match filter_vars a with
     | [] -> ()
     | vs -> fprintf oc "where %a, " (p_list dict "" pr " and ") vs
     end;
     fprintf oc "OF %a])\n" (p_list dict "" pr_hyp " ") proof.conc;
  | Rcut (e1) ->
     iprintf i oc "show FALSE\n";
     iprintf i oc "proof (rule zenon_em [of \"%a\"])\n" (p_expr dict) e1;
     let rec p_sub dict l1 l2 =
       match l1, l2 with
       | h::hs, t::ts ->
          let dict2 = p_sequent hyps (iinc i) dict oc h in
          p_tree hyps (iinc i) dict2 oc t;
          iprintf i oc "%s\n" (if hs = [] then "qed" else "next");
          p_sub dict hs ts;
       | [], [] -> ()
       | _ -> assert false
     in p_sub dict [[e1]; [enot e1]] proof.hyps;
  | Raxiom (e1) ->
     let n_e1 = hname hyps e1 in
     let n_ne1 = hname hyps (enot e1) in
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule notE [OF %s %s])\n" n_ne1 n_e1;
  | Rdefinition (name, s, args, body, None, conc, hyp) ->
     let n_conc = hname hyps conc in
     let n_hyp = hname hyps hyp in
     iprintf i oc "have %s_%s: \"%a == %a\"" n_hyp n_conc
             (p_expr dict) hyp (p_expr dict) conc;
     let (p_h, dict1) = mk_pat dict hyp in
     let (p_c, dict2) = mk_pat dict1 conc in
     fprintf oc " (is \"%s == %s\")\n" p_h p_c;
     iprintf i oc "by (unfold %s)\n" name;
     iprintf i oc "have %s: \"%a\"" n_hyp (p_expr dict2) hyp;
     let dict3 = p_is dict2 oc hyp in
     iprintf i oc "by (unfold %s_%s, fact %s)\n" n_hyp n_conc n_conc;
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     p_tree hyps i dict3 oc t;
  | Rdefinition _ -> assert false
  | Rnotequal (Eapp (f, args1, _) as e1, (Eapp (g, args2, _) as e2)) ->
     assert (f = g);
     let e = enot (eapp ("=", [e1; e2])) in
     iprintf i oc "show FALSE\n";
     iprintf i oc "proof (rule zenon_noteq [of \"%a\"])\n" (p_expr dict) e2;
     let pr d x y z = p_sub_equal hyps (iinc i) d oc x y z in
     let dict2 = list_fold_left3 pr dict args1 args2 proof.hyps in
     let mk l = enot (eapp ("=", [eapp (f, l); e2])) in
     p_subst hyps i dict2 oc mk args1 args2 [] e;
  | Rnotequal _ -> assert false
  | Rpnotp (Eapp (p, args1, _) as pp, (Enot (Eapp (q, args2, _), _) as np)) ->
     assert (p = q);
     iprintf i oc "show FALSE\n";
     iprintf i oc "proof (rule notE [OF %s])\n" (hname hyps np);
     let pr d x y z = p_sub_equal hyps (iinc i) d oc x y z in
     let dict2 = list_fold_left3 pr dict args1 args2 proof.hyps in
     let mk l = eapp (p, l) in
     p_subst hyps i dict2 oc mk args1 args2 [] pp;
  | Rpnotp _ -> assert false
  | Rnoteq e1 ->
     let neq = enot (eapp ("=", [e1; e1])) in
     let n_neq = hname hyps neq in
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule zenon_noteq [OF %s])\n" n_neq;
  | Reqsym (e1, e2) ->
     let eq = eapp ("=", [e1; e2]) in
     let n_eq = hname hyps eq in
     let neq = enot (eapp ("=", [e2; e1])) in
     let n_neq = hname hyps neq in
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule zenon_eqsym [OF %s %s])\n" n_eq n_neq;
  | Rnottrue ->
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule zenon_nottrue [OF %s])\n" (hname hyps (enot etrue))
  | Rfalse ->
     iprintf i oc "show FALSE\n";
     iprintf i oc "by (rule %s)\n" (hname hyps efalse);
  | RcongruenceLR (p, a, b) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let h0 = eapp ("=", [a; b]) in
     let h1 = apply p a in
     let c = apply p b in
     iprintf i oc "have %s: \"%a\"" (hname hyps c) (p_expr dict) c;
     let dict2 = p_is dict oc c in
     iprintf i oc "by (rule subst [where P=\"%a\", OF %s %s])\n"
             (p_expr dict2) p (hname hyps h0) (hname hyps h1);
     p_tree hyps i dict2 oc t;
  | RcongruenceRL (p, a, b) ->
     let t = match proof.hyps with [t] -> t | _ -> assert false in
     let h0 = eapp ("=", [b; a]) in
     let h1 = apply p a in
     let c = apply p b in
     iprintf i oc "have %s: \"%a\"" (hname hyps c) (p_expr dict) c;
     let dict2 = p_is dict oc c in
     iprintf i oc "by (rule ssubst [where P=\"%a\", OF %s %s])\n"
             (p_expr dict2) p (hname hyps h0) (hname hyps h1);
     p_tree hyps i dict2 oc t;

and p_alpha hyps i dict oc lem h0 hs sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let n_h0 = hname hyps h0 in
  let pr_h (dict, j) h =
    if List.memq h t.conc then begin
      iprintf i oc "have %s: \"%a\"" (hname hyps h) (p_expr dict) h;
      let dict2 = p_is dict oc h in
      iprintf i oc "by (rule zenon_%s_%d [OF %s])\n" lem j n_h0;
      (dict2, j+1)
    end else (dict, j+1)
  in
  let (dict3, _) = List.fold_left pr_h (dict, 0) hs in
  p_tree hyps i dict3 oc t;

and p_beta hyps i dict oc lem h0 hs sub =
  let n0 = hname hyps h0 in
  iprintf i oc "show FALSE\n";
  iprintf i oc "proof (rule zenon_%s [OF %s])\n" lem n0;
  let rec p_sub dict l1 l2 =
    match l1, l2 with
    | h::hs, t::ts ->
       let dict2 = p_sequent hyps (iinc i) dict oc h in
       p_tree hyps (iinc i) dict2 oc t;
       iprintf i oc "%s\n" (if hs = [] then "qed" else "next");
       p_sub dict hs ts;
    | [], [] -> ()
    | _ -> assert false
  in
  p_sub dict hs sub;

and p_gamma hyps i dict oc lem neg lam e conc sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let (ng, negs) = if neg then (enot, "~") else ((fun x -> x), "") in
  let body = ng (apply lam e) in
  let n_body = hname hyps body in
  iprintf i oc "have %s: \"%s%a\"" n_body negs (p_apply dict) (lam, e);
  let dict2 = p_is dict oc body in
  iprintf i oc "by (rule zenon_%s_0 [of \"%a\" \"%a\", OF %s])\n"
          lem (p_expr dict2) lam (p_expr dict2) e (hname hyps conc);
  p_tree hyps i dict2 oc t;

and p_delta hyps i dict oc lem neg lam e conc sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let (ng, negs) = if neg then (enot, "~") else ((fun x -> x), "") in
  let body = ng (apply lam e) in
  let n_body = hname hyps body in
  iprintf i oc "have %s: \"%s%a\"" n_body negs (p_apply dict) (lam, e);
  let dict2 = p_is dict oc body in
  iprintf i oc "by (rule zenon_%s_0 [of \"%a\", OF %s])\n"
          lem (p_expr dict2) lam (hname hyps conc);
  p_tree hyps i dict2 oc t;

and p_sub_equal hyps i dict oc e1 e2 prf =
  let eq = eapp ("=", [e1; e2]) in
  if Expr.equal e1 e2 || List.exists (Expr.equal eq) prf.conc
  then dict
  else begin
    let n_eq = enot (eq) in
    iprintf i oc "have %s: \"%a\"" (hname hyps eq) (p_expr dict) eq;
    let dict2 = p_is dict oc eq in
    let rev_eq = eapp ("=", [e2; e1]) in
    if List.exists (Expr.equal rev_eq) prf.conc then begin
      iprintf i oc "by (rule sym [OF %s])\n" (hname hyps rev_eq);
    end else begin
      iprintf i oc "proof (rule zenon_nnpp [of \"%a\"])\n" (p_expr dict2) eq;
      let dict3 = p_sequent hyps (iinc i) dict2 oc [n_eq] in
      p_tree hyps (iinc i) dict3 oc prf;
      iprintf i oc "qed\n";
    end;
    dict2
  end

and p_subst hyps i dict oc mk l1 l2 rl2 prev =
  match l1, l2 with
  | [], [] ->
     iprintf (iinc i) oc "thus \"%a\" .\n" (p_expr dict) prev;
     iprintf i oc "qed\n";
  | h1 :: t1, h2 :: t2 ->
     if Expr.equal h1 h2 then
       p_subst hyps i dict oc mk t1 t2 (h2 :: rl2) prev
     else begin
       let newrl2 = h2 :: rl2 in
       let x = newvar () in
       let p = elam (x, "", mk (List.rev_append rl2 (x :: t1))) in
       let e = apply p h2 in
       let n_e = hname hyps e in
       iprintf (iinc i) oc "have %s: \"%a\"" n_e (p_expr dict) e;
       let dict2 = p_is dict oc e in
       let eq = eapp ("=", [h1; h2]) in
       iprintf (iinc i) oc "by (rule subst [where P=\"%a\", OF %s], fact %s)\n"
               (p_expr dict2) p (hname hyps eq) (hname hyps prev);
       p_subst hyps i dict2 oc mk t1 t2 newrl2 e;
     end;
  | _, _ -> assert false
;;

let p_lemma hyps i dict oc lem =
  iprintf i oc "have %s: \"" lem.name;
  let f (ty, e) accu =
    match e with
    | Evar (x, _) -> x :: accu
    | Etau _ -> accu
    | _ -> assert false
  in
  let params = List.fold_right f lem.params [] in
  List.iter (fprintf oc "!!%s. ") params;
  List.iter (fun x -> fprintf oc "%a ==> " (p_expr dict) x) lem.proof.conc;
  fprintf oc "FALSE\"";

  let f (pats, dict) e = let (p, dict1) = mk_pat dict e in (p :: pats, dict1) in
  let (pats, dict1) = List.fold_left f ([], dict) lem.proof.conc in
  if List.for_all ((=) "_") pats then begin
    fprintf oc "\n";
  end else begin
    fprintf oc " (is \"";
    List.iter (fprintf oc "%s ==> ") (List.rev pats);
    fprintf oc "FALSE\")\n";
  end;
  iprintf i oc "proof -\n";
  List.iter (fun p -> iprintf (iinc i) oc "fix \"%s\"\n" p) params;
  let p_asm dict x =
    iprintf (iinc i) oc "assume %s:\"%a\"" (hname hyps x) (p_expr dict) x;
    p_is dict oc x
  in
  let dict2 = List.fold_left p_asm dict1 lem.proof.conc in
  p_tree hyps (iinc i) dict2 oc lem.proof;
  iprintf i oc "qed\n";
;;

let rec get_ngoal phrases =
  match phrases with
  | [] -> enot (efalse)
  | Phrase.Hyp (n, e, _) :: t when n = goal_name -> e
  | _ :: t -> get_ngoal t
;;

module HE = Hashtbl.Make (Expr);;

let mk_hyp_dict phrases =
  let f hyps p =
    match p with
    | Phrase.Hyp ("", _, _) -> hyps
    | Phrase.Hyp (name, e, _) -> Hypdict.add (Index.get_number e) name hyps;
    | _ -> hyps
  in
  List.fold_left f Hypdict.empty phrases
;;

type nary_rule =
  | Nary_case of int * bool
  | Nary_record of int
;;

let rec get_nary_rules accu prf =
  let accu1 =
    match prf.rule with
    | Rextension (_, "zenon_case", _, _, hs) ->
       let arity = List.length hs - 1 in
       let other =
         let rec loop l =
           match l with
           | [ [x] ] -> false
           | [ [x; y] ] -> true
           | h :: t -> loop t
           | _ -> assert false
         in loop hs
       in
       if arity > 5 then Nary_case (arity, other) :: accu else accu
    | Rextension (_, "zenon_notin_recordset", _, _, hs) ->
       let arity = List.length hs - 2 in
       if arity > 7 then Nary_record (arity) :: accu else accu
    | _ -> accu
  in
  List.fold_left get_nary_rules accu1 prf.hyps
;;

let add_nary_rules oc lemmas =
  let f lem = get_nary_rules [] lem.proof in
  let rules = List.flatten (List.map f lemmas) in
  let rules1 = Misc.list_sort_unique Stdlib.compare rules in
  let f r =
    match r with
    | Nary_case (n, oth) -> Isar_case.print_case "have" n oth oc
    | Nary_record (n) -> Isar_case.print_record "have" n oc
  in
  List.iter f rules1;
;;

let p_theorem oc thm phrases lemmas =
  let ngoal = get_ngoal phrases in
  let goal =
    match ngoal with
    | Enot (e1, _) -> e1
    | _ -> assert false
  in
  let hyps = List.filter (fun x -> x <> ngoal) thm.proof.conc in
  let realhypnames = mk_hyp_dict phrases in
  let hypnames = Hypdict.empty in
  iprintf 0 oc "proof (rule zenon_nnpp)\n";
  add_nary_rules oc (thm :: lemmas);
  let i = iinc 0 in
  let p_asm dict x =
    iprintf i oc "have %s:\"%a\"" (hname hypnames x) (p_expr dict) x;
    let dict2 = p_is dict oc x in
    if Hypdict.mem (Index.get_number x) realhypnames then begin
      iprintf i oc "using %s by blast\n" (hname realhypnames x);
    end else begin
      iprintf i oc "by fact\n";
    end;
    dict2
  in
  let dict3 = List.fold_left p_asm dict_empty hyps in
  List.iter (p_lemma hypnames i dict3 oc) lemmas;
  let dict4 = p_sequent hypnames i dict3 oc [enot (goal)] in
  p_tree hypnames i dict4 oc thm.proof;
  iprintf 0 oc "qed\n";
;;

let rec p_lemmas oc llp phrases lemmas =
  match llp with
  | [] -> assert false
  | [x] -> p_theorem oc x phrases (List.rev lemmas);
  | h::t -> p_lemmas oc t phrases (h::lemmas);
;;

let output oc phrases ppphrases llp =
  if !Globals.ctx_flag then begin
    fprintf oc "(* BEGIN-CONTEXT *)\n";
    fprintf oc "theory zenon_tmp_theory imports Constant Zenon begin\n";
    let f p =
      match p with
      | Phrase.Hyp ("", _, _) -> ()
      | Phrase.Hyp (name, e, _) when name <> Namespace.goal_name ->
         fprintf oc "axioms %s: \"%a\"\n" name (p_expr dict_empty) e
      | Phrase.Hyp _ -> ()
      | Phrase.Def (DefReal (name, sym, args, body, None)) ->
         let isym = tr_prefix sym in
         fprintf oc "consts \"%s\" :: \"[%a] \\<Rightarrow> c\"\n" isym
                 (p_list dict_empty "c" (fun _ _ _ -> ()) ",") args;
         fprintf oc "defs \"%s\": \"%s(%a) \\<equiv> %a\"\n" name isym
                 (p_list dict_empty "" p_expr ",") args
                 (p_expr dict_empty) body;
      | Phrase.Def _ -> assert false
      | Phrase.Sig _ -> failwith "signatures not implemented in isar output"
      | Phrase.Inductive _ ->
         failwith "inductives not implemented in isar output"
    in
    List.iter f phrases;
    fprintf oc "theorem zenon_tmp_thm:\n";
    let f p =
      match p with
      | Phrase.Hyp ("", e, _) ->
         fprintf oc "assumes \"%a\"\n" (p_expr dict_empty) e;
      | _ -> ()
    in
    List.iter f phrases;
    let f p =
      match p with
      | Phrase.Hyp (name, Enot (e, _), _) when name = Namespace.goal_name ->
         fprintf oc "shows \"%a\"\n" (p_expr dict_empty) e;
      | _ -> ()
    in
    List.iter f phrases;
    fprintf oc "(* END-CONTEXT *)\n";
  end;
  if not !Globals.quiet_flag then fprintf oc "(* BEGIN-PROOF *)\n";
  p_lemmas oc llp phrases [];
  if not !Globals.quiet_flag then fprintf oc "(* END-PROOF *)\n";
  !Coqterm.constants_used
;;
