(*  Copyright 2004 INRIA  *)

open Expr;;
open Misc;;
open Mlproof;;
open Printf;;

let ( === ) = ( = );;
let ( = ) = ();;
let string_equal x y = String.compare x y == 0;;

let tblsize = 997;;  (* reduce to 17 for debugging *)

module HE = Hashtbl.Make (Expr);;

let allforms = (HE.create tblsize : int HE.t);;

type sym_table = (string, expr list ref) Hashtbl.t;;

let posforms = (Hashtbl.create tblsize : sym_table);;
let negforms = (Hashtbl.create tblsize : sym_table);;

type formula_rec = {
  mutable present : bool;
  mutable proofs : (Mlproof.proof * int ref * formula_rec array) list;
};;
let proofs = (HE.create tblsize : formula_rec HE.t);;
let new_forms = ref [];;

exception No_head;;

type head = Sym of string | Tau of expr | Meta of expr;;

let get_head e =
  match e with
  | Eapp (s, _, _) | Evar (s, _)
  -> Sym s
  | Emeta _ -> Meta e
  | Etau _ -> Tau e
  | Etrue -> Sym "$true"
  | Efalse -> Sym "$false"
  | Eall _ -> Sym "A."
  | Eex _ -> Sym "E."
  | _ -> raise No_head
;;

let add_element tbl k v =
  try
    let lr = Hashtbl.find tbl k in
    lr := v :: !lr
  with Not_found ->
    Hashtbl.add tbl k (ref [v]);
;;

let remove_element tbl k v =
  let lr = Hashtbl.find tbl k in
  match !lr with
  | [] -> assert false
  | [h] -> Hashtbl.remove tbl k;
  | h::t when Expr.equal h v -> lr := t;
  | _ -> ()
;;

(* ==== *)

let act_head action tbl key v =
  try
    match get_head key with
    | Sym s -> action tbl s v
    | Tau e -> action tbl "t." v
    | Meta e -> action tbl "" v
  with No_head -> ()
;;

let negpos action e =
  match e with
  | Enot (f, _) -> act_head action negforms f e;
  | f -> act_head action posforms f e;
;;

let cur_num_forms = ref 0;;

let get_all () = HE.fold (fun e g l -> (e, g) :: l) allforms [];;

let member e = HE.mem allforms e;;

let get_goalness e = HE.find allforms e;;
let add_g e = (e, get_goalness e);;

let find_pos s =
  try List.map add_g !(Hashtbl.find posforms s)
  with Not_found -> []
;;

let find_neg s =
  try List.map add_g !(Hashtbl.find negforms s)
  with Not_found -> []
;;

(* ==== *)

type direction = Left | Right | Both;;

type trans_table = (string * head, expr list ref) Hashtbl.t;;

let pos_trans_left = (Hashtbl.create tblsize : trans_table);;
let pos_trans_right = (Hashtbl.create tblsize : trans_table);;

let rec do_trans action e =
  match e with
  | Eapp (r, [e1; e2], _) ->
      action pos_trans_left (r, get_head e1) e;
      action pos_trans_right (r, get_head e2) e;
  | _ -> assert false
;;

let add_trans e =
  do_trans add_element e;
;;

let try_find tbl k =
  try !(Hashtbl.find tbl k)
  with Not_found -> []
;;

let find_all_rel tbl rel =
  let f (r, _) elr accu =
    if string_equal r rel then !elr @@ accu else accu
  in
  Hashtbl.fold f tbl []
;;

let find_trans_left rel head =
  List.map add_g (try_find pos_trans_left (rel, head))
;;

let find_trans_right rel head =
  List.map add_g (try_find pos_trans_right (rel, head))
;;

let find_all_head tbl head =
  let f (_, h) elr accu =
    match head, h with
    | Meta e1, Meta e2 when e1 == e2 -> !elr @@ accu
    | Sym s1, Sym s2 when s1 === s2 -> !elr @@ accu
    | Tau t1, Tau t2 when t1 === t2 -> !elr @@ accu
    | _, _ -> accu
  in
  Hashtbl.fold f tbl []
;;

let remove_trans e =
  match e with
  | Eapp (r, [e1; e2], _) ->
     begin try
       remove_element pos_trans_left (r, get_head e1) e;
     with No_head | Not_found -> ()
     end;
     begin try
       remove_element pos_trans_right (r, get_head e2) e;
     with No_head | Not_found -> ()
     end;
  | _ -> ()
;;

let neg_trans_left = (Hashtbl.create tblsize : trans_table);;
let neg_trans_right = (Hashtbl.create tblsize : trans_table);;

type head_table = (head, expr list ref) Hashtbl.t;;

let all_neg_trans_left = (Hashtbl.create tblsize : head_table);;
let all_neg_trans_right = (Hashtbl.create tblsize : head_table);;

let add_negtrans e =
  match e with
  | Enot (Eapp (r, [e1; e2], _), _) ->
      begin try
        add_element neg_trans_left (r, get_head e1) e;
        add_element all_neg_trans_left (get_head e1) e;
      with No_head -> ()
      end;
      begin try
        add_element neg_trans_right (r, get_head e2) e;
        add_element all_neg_trans_right (get_head e2) e;
      with No_head -> ()
      end;
  | _ -> assert false;
;;

let remove_negtrans e =
  match e with
  | Enot (Eapp (r, [e1; e2], _), _) ->
      begin try
        remove_element neg_trans_left (r, get_head e1) e;
        remove_element all_neg_trans_left (get_head e1) e;
      with No_head | Not_found -> ()
      end;
      begin try
        remove_element neg_trans_right (r, get_head e2) e;
        remove_element all_neg_trans_right (get_head e2) e;
      with No_head | Not_found -> ()
      end;
  | _ -> ()
;;

let find_negtrans_left rel head =
  List.map add_g (try_find neg_trans_left (rel, head))
;;

let find_negtrans_right rel head =
  List.map add_g (try_find neg_trans_right (rel, head))
;;

let find_all_negtrans_left head =
  List.map add_g (try_find all_neg_trans_left head)
;;

let find_all_negtrans_right head =
  List.map add_g (try_find all_neg_trans_right head)
;;

(* ==== *)

let eq_lr = (HE.create tblsize : Expr.t HE.t);;
let eq_rl = (HE.create tblsize : Expr.t HE.t);;
let neq_lr = (HE.create tblsize : Expr.t HE.t);;
let neq_rl = (HE.create tblsize : Expr.t HE.t);;

let add_eq e =
  match e with
  | Eapp ("=", [e1; e2], _) ->
     HE.add eq_lr e1 e2;
     HE.add eq_rl e2 e1;
  | Enot (Eapp ("=", [e1; e2], _), _) ->
     HE.add neq_lr e1 e2;
     HE.add neq_rl e2 e1;
  | _ -> ()
;;

let remove_eq e =
  match e with
  | Eapp ("=", [e1; e2], _) ->
     HE.remove eq_lr e1;
     HE.remove eq_rl e2;
  | Enot (Eapp ("=", [e1; e2], _), _) ->
     HE.remove neq_lr e1;
     HE.remove neq_rl e2;
  | _ -> ()
;;

let find_eq_lr e = HE.find_all eq_lr e;;
let find_eq_rl e = HE.find_all eq_rl e;;
let find_neq_lr e = HE.find_all neq_lr e;;
let find_neq_rl e = HE.find_all neq_rl e;;

let find_eq e =
  List.map (fun x -> eapp ("=", [e; x])) (find_eq_lr e)
  @ List.map (fun x -> eapp ("=", [x; e])) (find_eq_rl e);;
let find_neq e =
  List.map (fun x -> enot (eapp ("=", [e; x]))) (find_neq_lr e)
  @ List.map (fun x -> enot (eapp ("=", [x; e]))) (find_neq_rl e);;

(* ==== *)

let meta_set = (HE.create tblsize : unit HE.t);;

let add_meta_set e =
  match e with
  | Eapp ("TLA.in", [Emeta _; e1], _)
  | Enot (Eapp ("TLA.in", [Emeta _; e1], _), _)
    -> HE.add meta_set e1 ()
  | _ -> ()
;;

let remove_meta_set e =
  match e with
  | Eapp ("TLA.in", [Emeta _; e1], _)
  | Enot (Eapp ("TLA.in", [Emeta _; e1], _), _)
    -> HE.remove meta_set e1
  | _ -> ()
;;

let is_meta_set e = HE.mem meta_set e;;

(* ==== *)

let eq_str = ref [];;
let str_eq = ref [];;

let add_str e =
  match e with
  | Eapp ("=", [e1; Eapp ("$string", [Evar (str, _)], _)], _) ->
     eq_str := (e1, str) :: !eq_str
  | Eapp ("=", [Eapp ("$string", [Evar (str, _)], _); e2], _) ->
     str_eq := (e2, str) :: !str_eq
  | _ -> ()
;;

let remove_str e =
  match e with
  | Eapp ("=", [e1; Eapp ("$string", [Evar (str, _)], _)], _) ->
     eq_str := (match !eq_str with _ :: t -> t | _ -> assert false)
  | Eapp ("=", [Eapp ("$string", [Evar (str, _)], _); e2], _) ->
     str_eq := (match !str_eq with _ :: t -> t | _ -> assert false)
  | _ -> ()
;;

let find_eq_str () = !eq_str;;
let find_str_eq () = !str_eq;;

(* ==== *)

let add e g =
  HE.add allforms e g;
  add_eq e;
  add_str e;
  incr cur_num_forms;
  if !cur_num_forms > !Globals.top_num_forms
  then Globals.top_num_forms := !cur_num_forms;
  negpos add_element e;
  begin try (HE.find proofs e).present <- true with Not_found -> (); end;
  new_forms := e :: !new_forms;
;;

let remove e =
  decr cur_num_forms;
  remove_trans e;
  remove_negtrans e;
  negpos remove_element e;
  remove_str e;
  remove_eq e;
  HE.remove allforms e;
  begin try (HE.find proofs e).present <- false with Not_found -> (); end;
;;

(* ==== *)

let suspects = ref [];;

let add_proof p =
  incr Globals.stored_lemmas;
  let get_record f =
    begin try HE.find proofs f
    with Not_found ->
      let r = {present = HE.mem allforms f; proofs = []} in
      HE.add proofs f r;
      r
    end
  in
  let recs = Array.of_list (List.map get_record p.mlconc) in
  suspects := [(p, ref 0, recs)] :: !suspects;
;;

(* FIXME essayer:
   changer la structure de donnees pour utiliser des refcounts
*)

let search_proof () =
  let do_form f =
    try
      let r = HE.find proofs f in
      if r.present then begin
        suspects := r.proofs :: !suspects;
        r.proofs <- [];
      end;
    with Not_found -> ()
  in
  let fs = !new_forms in
  new_forms := [];
  List.iter do_form fs;
  let rec loop () =
    match !suspects with
    | [] -> None
    | [] :: t2 -> suspects := t2; loop ()
    | ((p, cur, recs) as lem :: t1) :: t2 ->
        begin try
          for i = !cur to Array.length recs - 1 do
            if not recs.(i).present then begin
              suspects := t1 :: t2;
              recs.(i).proofs <- lem :: recs.(i).proofs;
              cur := i+1;
              raise Exit;
            end
          done;
          for i = 0 to !cur-1 do
            if not recs.(i).present then begin
              suspects := t1 :: t2;
              recs.(i).proofs <- lem :: recs.(i).proofs;
              cur := i+1;
              raise Exit;
            end
          done;
          Some p
        with Exit -> loop ()
        end
  in
  loop ()
;;

(* ==== *)

let defs = (Hashtbl.create tblsize : (string, definition) Hashtbl.t);;

let add_def d =
  match d with
  | DefReal (_, s, args, body, _) -> Hashtbl.add defs s d;
  | DefPseudo (h, s, args, body) -> Hashtbl.add defs s d;
  | DefRec (_, s, args, body) -> Hashtbl.add defs s d;
;;
let has_def s = Hashtbl.mem defs s;;
let get_def s =
  let d = Hashtbl.find defs s in
  match d with
  | DefReal (_, s, params, body, _) -> (d, params, body)
  | DefPseudo (hyp, s, params, body) -> (d, params, body)
  | DefRec (_, s, params, body) -> (d, params, body)
;;

(* ==== *)

let metas = (HE.create tblsize : int HE.t);;

let add_meta e i = HE.add metas e i;;
let remove_meta e = HE.remove metas e;;
let get_meta e = HE.find metas e;;

(* ==== *)

let cur_num = ref (-1);;
let numforms = (HE.create tblsize : int HE.t);;
let formnums = ref ([| |] : expr array);;
let dummy = evar " *** Index.dummy *** ";;

let ext_set tbl i x =
  while i >= Array.length !tbl do
    let len = Array.length !tbl in
    let new_len = 2 * len + 1 in
    let new_tbl = Array.make new_len dummy in
    Array.blit !tbl 0 new_tbl 0 len;
    tbl := new_tbl;
  done;
  !tbl.(i) <- x;
;;

let rec expr o ex =
  let pr = eprintf in
  let print_var b v =
    match v with
    | Evar (s, _) -> eprintf "%s" s
    | _ -> assert false
  in
  match ex with
  | Evar (v, _) -> pr "%s" v;

  | Emeta (e, _) -> pr "%s#" Namespace.meta_prefix;
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
  | Eall (v, t, e, _) when t === Namespace.univ_name ->
      pr "(A. ((%a) " print_var v; expr o e; pr "))";
  | Eall (v, t, e, _) ->
      pr "(A. ((%a \"%s\") " print_var v t; expr o e; pr "))";
  | Eex (v, t, e, _) when t === Namespace.univ_name ->
      pr "(E. ((%a) " print_var v; expr o e; pr "))";
  | Eex (v, t, e, _) ->
      pr "(E. ((%a \"%s\") " print_var v t; expr o e; pr "))";
  | Etau (v, t, e, _) when t === Namespace.univ_name ->
      pr "(t. ((%a) " print_var v; expr o e; pr "))";
  | Etau (v, t, e, _) ->
      pr "(t. ((%a \"%s\") " print_var v t; expr o e; pr "))";
  | Elam (v, t, e, _) when t === Namespace.univ_name ->
      pr "((%a) " print_var v; expr o e; pr ")";
  | Elam (v, t, e, _) ->
      pr "((%a \"%s\") " print_var v t; expr o e; pr ")";
;;

let dprint_expr e = expr () e;;

let get_number e =
  begin try HE.find numforms e
  with Not_found ->
    incr cur_num;
    HE.add numforms e !cur_num;
    ext_set formnums !cur_num e;
    if !Globals.debug_flag then begin
      Printf.eprintf "%x --> " !cur_num;
      dprint_expr e;
      Printf.eprintf "\n";
    end;
    !cur_num
  end
;;

let get_formula i =
  if i < 0 || i >= Array.length !formnums then raise Not_found;
  if !formnums.(i) == dummy then raise Not_found;
  !formnums.(i)
;;

let make_tau_name p =
  match p with
  | Etau (Evar (v, _), _, _, _) when is_prefix "zenon_" v ->
     Printf.sprintf "%s_%s" Namespace.tau_prefix (base26 (get_number p))
  | Etau (Evar (v, _), _, _, _) ->
     Printf.sprintf "%s%s_%s" Namespace.tau_prefix v (base26 (get_number p))
  | _ -> assert false
;;
