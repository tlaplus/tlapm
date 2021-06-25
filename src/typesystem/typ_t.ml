(************************************************************************
*
*  Typ_t.ml -- Types
*
*
*  Created by Hernán Vanzetto on 23 Oct 2013.
*
************************************************************************)

open Ext
open Property

open Expr.T
open Expr.Subst
open Expr.Visit

open Printf
open List

module B = Builtin
module Smt = Smtcommons

(****************************************************************************)

open Format
open Fmtutil
open Tla_parser   (** for [fmt_expr] *)

exception Typeinf_failed

(****************************************************************************)

type t =
  | Int | Str | Bool
  | TyAtom of string                (** Atomic type *)
  | Top                             (** Only for CHOOSE *)
  | TyVar of ty_subst list * string (** Type variable with delayed substitution *)
  | Set of t                        (** Power set type *)
  | Func of string * t * t          (** Dependent function type *)
  | Ref of string * t * tref        (** Refinement type *)
  | Rec of (string * t) list
  | Rec_dot of t * string
  | TyPlus of t list
  | TyTimes of t list
  | Tbase of t                      (** Base of refinement *)
  | Tdom of t                       (** Domain *)
  | Tcod of t                       (** Co-domain *)
and tref =
  | Ex of hyp list * expr
  | Ph of (ty_subst list * plhdr)
and plhdr = string									(** Placeholder (for refinement predicates) *)
and ty_subst = string * hyp list * expr * t		(** Delayed substitution *)

let ctr_funarg = ref 0
let fresh_tyterm () = "x" ^ string_of_int (incr ctr_funarg ; !ctr_funarg)

(** Makes a trivial refinement type with base type [t] *)
let mk_ref t = Ref (fresh_tyterm (), t, Ex ([], noprops (Internal B.TRUE)))

(**************************************************************************)
(** Type annotations, as properties attached to expressions *)

let typeprop : t pfuncs = Property.make "Backend.Smt.TLAType"
let ( <<< ) e t = assign e typeprop t
let optype v = try Some (Property.get v typeprop) with Not_found -> None
let has_type v = Property.has v typeprop

(**************************************************************************)

let is_atomic_type = function
  | Int | Bool | Str | Top -> true
  (* | Ref (_, t, Ex(_,{core = Internal B.TRUE})) when is_atomic_type t -> true *)
  | TyAtom _ -> true
  | _ -> false

let add_x_ctx x t cx =
  Smt.add_bs_ctx [noprops x <<< t, Unknown, No_domain] cx

let add_x_ref x t =
  function Ex (cx,e) -> Ex (add_x_ctx x t cx,e) | p -> p

let add_x_ref_last x t =
  function
    | Ex (cx,e) ->
        let v = noprops x <<< t in
        let cx' = cx @ [Fresh (v, Shape_expr, Unknown, Unbounded) @@ v] in
        Ex (cx',e)
    | p -> p

let dom_ss ss = map (fun (v,_,_,_) -> v) ss
(* let expr_ss ss = map (fun (v,cx,e,t) ->
  add_x_ctx v t cx,
  noprops (Apply (noprops (Internal B.Eq), [noprops (Ix 1) ; app_expr (shift 1) e]))) ss *)

let map_subst_t f =
	let proj4 (_,_,_,t) = t in
	map (fun s -> f (proj4 s))

(** Set of free type-variable identifiers *)
let rec fv = function
  | Int | Str | Bool | TyAtom _ -> []
  | Top -> []
  | TyVar (ss,a) -> [a] @ (fv_ss ss)
  | Set t -> fv t
  | Func (x,t1,t2) -> fv t1 @ fv t2
  | Ref (x,t,Ex _) -> fv t
  | Ref (x,t,Ph (ss,_)) -> fv t @ fv_ss ss
  | Rec rs -> flatten (map (fun (_,t) -> fv t) rs)
  | Rec_dot (t,_) -> fv t
  | TyPlus ts -> flatten (map fv ts)
  | TyTimes ts -> flatten (map fv ts)
  | Tbase t -> fv t
  | Tdom t -> fv t
  | Tcod t -> fv t
and fv_ss ss =
  flatten (map_subst_t fv ss)

(** Set of free (Expr.T.expr) variable symbols *)
let rec expr_fv : t -> string list = function
  | Int | Str | Bool | TyAtom _ -> []
  | Top -> []
  | TyVar (ss,a) -> expr_fv_ss ss
  | Set t -> expr_fv t
  | Func (x,t1,t2) ->
      expr_fv t1 @ (Smt.subtract (expr_fv t2) x)
  | Ref (x,t,Ex (cx,e)) ->
      (* expr_fv t @ (Smt.subtract (Smt.free_vars (add_x_ctx x t cx) e) x) *)
      expr_fv t @ (Smt.subtract (Smt.fv_expr ((),Smt.to_scx (add_x_ctx x t cx)) e) x)
  | Ref (x,t,Ph _) ->
      expr_fv t
  | Rec rs -> flatten (map (fun (_,t) -> expr_fv t) rs)
  | Rec_dot (t,_) -> expr_fv t
  | TyPlus ts ->
      flatten (map expr_fv ts)
  | TyTimes ts ->
      flatten (map expr_fv ts)
  | Tbase t -> expr_fv t
  | Tdom t -> expr_fv t
  | Tcod t -> expr_fv t
and expr_fv_ss ss =
  flatten (map_subst_t expr_fv ss)

let tmap (f:t -> t) t =
  let fss f ss = map (fun (v,cx,e,t) -> v,cx,e,f t) ss in
  match t with
  | Set t -> Set (f t)
  | Ref (x,t,Ex (cx,e)) -> Ref (x,f t,Ex (cx,e))
  | Ref (x,t,Ph (ss,p)) -> Ref (x,f t,Ph (fss f ss,p))
  | Func (x,t1,t2) -> Func (x, f t1, f t2)
  | Rec rs -> Rec (map (fun (h,t) -> (h, f t)) rs)
  | Rec_dot (t,h) -> Rec_dot (f t, h)
  | TyPlus ts -> TyPlus (map f ts)
  | TyTimes ts -> TyTimes (map f ts)
  | Tbase t -> Tbase (f t)
  | Tdom t -> Tdom (f t)
  | Tcod t -> Tcod (f t)
  | TyVar (ss,a) -> TyVar (fss f ss,a)
  | t -> t

(** Apply explicit substitutions [ss] to refinement predicate [cx,e] *)
let rec add_exp_substs cx e = function
  | (v,cx',e',t) :: ss ->       (** CHECK: cx' not used! *)
      let e' = Smt.opaque cx' e' in
      let cx,e = add_exp_substs cx e ss in
      let e = app_expr (scons (Ix 1 @@ e) (scons e' (shift 2))) e in          (** [Ix 1] is unchanged, [Ix 2] is substituted by [e'] *)
      cx, e
  | [] ->
      cx, e

(** Distribute substitution [ss] on type [t], and apply it on refinements *)
let rec subst_reduce ss t : t =
  (* Util.eprintf "!! simp : %a" pp (TySubst (ss,t)); *)
  (* Printf.eprintf "-- free_vars : %s\n" (String.concat "," (expr_fv t)); *)
  (* let ss = Smt.remove_repeated ss in *)
  begin match ss,t with
  | [], _ ->
      t
  | _, (Int | Bool | Str | TyAtom _ | Top) ->
      t
  | ss, TyVar (ss',a) ->
      TyVar (ss' @ ss, a)
  | ss, Set t ->
      Set (subst_reduce ss t)
  | ss, Func (x, t1, t2) ->
      Func (x, subst_reduce ss t1, subst_reduce ss t2)
  | ss, Ref (x,t,Ex (cx,e)) ->
      let cx,e = add_exp_substs cx e ss in    (** FIX it should need env *)
      Ref (x, t, Ex (cx,e))
  | (v,_,_,_) as s :: ss, Ref (x,t,Ph (ss',p))
    when not (mem v (dom_ss ss')) ->
      assert (v <> x);
      subst_reduce ss (Ref (x,t, Ph (s::ss',p)))
  | ss, Ref (x,t,Ph (ss',p)) ->
      Ref (x, subst_reduce ss t, Ph (ss' @ ss,p))
  | ss, Rec rs ->
      Rec (map (fun (h,t) -> h, subst_reduce ss t) rs)
  | ss, Rec_dot (t,h) ->
      Rec_dot (subst_reduce ss t, h)
  | ss, TyPlus ts ->
      TyPlus (map (subst_reduce ss) ts)
  | ss, TyTimes ts ->
      TyTimes (map (subst_reduce ss) ts)
  | ss, Tbase t ->
      Tbase (subst_reduce ss t)
  | ss, Tdom t ->
      Tdom (subst_reduce ss t)
  | ss, Tcod t ->
      Tcod (subst_reduce ss t)
  end

(** Substitution of type variable [a] for type [x] *)
let rec subst a x = function
  | TyVar (ss,a') ->
      let ss = subst_ss a x ss in
      if a = a' then subst_reduce ss x else TyVar (ss, a')
  | Set t -> Set (subst a x t)
  | Ref (x',t,r) -> Ref (x',subst a x t,subst_ref a x r)
  | Func (x',t1,t2) -> Func (x', subst a x t1, subst a x t2)
  | Rec rs -> Rec (map (fun (h,t) -> (h, subst a x t)) rs)
  | Rec_dot (t,h) -> Rec_dot (subst a x t, h)
  | TyPlus ts -> TyPlus (map (subst a x) ts)
  | TyTimes ts -> TyTimes (map (subst a x) ts)
  | Tbase t -> Tbase (subst a x t)
  | Tdom t -> Tdom (subst a x t)
  | Tcod t -> Tcod (subst a x t)
  | t -> t
and subst_ss a x = map (fun (v,cx,e,t) -> v,cx,e,subst a x t)   (** CHECK subst v by a? *)
and subst_ref a x = function
  | Ph (ss,p) -> Ph (subst_ss a x ss,p)
  | r -> r

(** Substitution of type variable identifiers [a] for [b] *)
let rec vsubst a b = function
  | TyVar (ss,a') ->
      let ss = ss_vsubst a b ss in
      TyVar (ss, if a = a' then b else a')
  | Set t -> Set (vsubst a b t)
  | Ref (x,t,Ex (cx,e)) -> Ref (x,vsubst a b t,Ex (cx,e))
  | Ref (x,t,Ph (ss,p)) -> Ref (x,vsubst a b t,Ph ((ss_vsubst a b ss), p))
  | Func (x',t1,t2) -> Func ((if a = x' then b else x'), vsubst a b t1, vsubst a b t2)
  | Rec rs -> Rec (map (fun (h,t) -> (h, vsubst a b t)) rs)
  | Rec_dot (t,h) -> Rec_dot (vsubst a b t, h)
  | TyPlus ts -> TyPlus (map (vsubst a b) ts)
  | TyTimes ts -> TyTimes (map (vsubst a b) ts)
  | Tbase t -> Tbase (vsubst a b t)
  | Tdom t -> Tdom (vsubst a b t)
  | Tcod t -> Tcod (vsubst a b t)
  | t -> t
and ss_vsubst a b = map (fun (v,cx,e,t) -> (if a = v then b else v),cx,e,vsubst a b t)

(** Syntactic equality *)
let rec eq t1 t2 =
  match t1, t2 with
  | Int, Int
  | Str, Str
  | Bool, Bool -> true
  | TyAtom t, TyAtom u -> t = u
  | Top, Top -> true
  | Top, t when is_atomic_type t -> true
  | t, Top when is_atomic_type t -> true
  | Top, Set t -> eq Top t
  | Set t, Top -> eq t Top
  | Top, _ -> true
  | _, Top -> true
  | TyVar ([],x), TyVar ([],y) ->
      x = y
  | TyVar (ss,x), TyVar (ss',y) ->
      x = y && ss_eq ss ss'
  | Set t1, Set t2 ->
      eq t1 t2
  | Func (_,t1,t2), Func (_,t1',t2') ->
      eq t1 t1' && eq t2 t2'
  | Ref (_,t,r), Ref (_,t',r') ->
      eq t t' && eq_ref r r'
  | Rec rs, Rec ts ->
      let rs = Smt.rec_sort rs in
      let ts = Smt.rec_sort ts in
      begin try for_all2 (fun (h,t) (i,u) -> h = i && eq t u) rs ts
      with _ -> false end
  | Rec_dot (t,h), Rec_dot (u,i) ->
      eq t u && h = i
  | TyPlus ts, TyPlus us ->
      for_all2 eq ts us
  | TyTimes ts, TyTimes us ->
      for_all2 eq ts us
  | Tbase t1, Tbase t2 -> eq t1 t2
  | Tdom t1, Tdom t2 -> eq t1 t2
  | Tcod t1, Tcod t2 -> eq t1 t2
  | _ ->
      false
and ss_eq ss ss' =
  try for_all2 (fun (v,cx,e,t) (v',cx',e',t') ->
    (* (if length cx <> length cx' then Printf.eprintf "** Warning! Contexts don't match for delayed substitutions.\n") ; *)
    (* cx_eq cx cx' && *) v = v' && Expr.Eq.expr e e' && eq t t'
    ) ss ss'
  with _ -> false
and eq_ref r1 r2 =
  match r1,r2 with
  | Ex (_,p), Ex (_,q) ->
      Expr.Eq.expr p q    																										(** Semantic equality: \A x. p(x) <=> q(x)   == Types.equiv t1 t2 *)
  | Ph (ss,p), Ph (ss',q) ->
      ss_eq ss ss' && p = q
  | _ -> false

(** Used to avoid recursive occurences of type variable [a]. *)
let occurs a t = List.mem a (fv t)

(** Expression [e] is an equality? *)
let is_eq e =
  match e.core with
  | Apply ({core = Internal B.Eq}, [{core = Ix 1} ; _]) -> true
  | _ -> false

(** Expression [e] is a disjunction of equalities? *)
let is_setenum e =
  match e.core with
  | List (Or,es) when for_all is_eq es -> true
  | _ -> false

(* let pp_cx ppf cx =
  let cx = mapi (fun i k -> Smt.lookup_id cx (i+1)) cx in
  Util.eprintf "@[<hov>%a@]" (pp_print_delimited pp_print_string) cx *)

(****************************************************************************)

let is_tyvar = function TyVar _ -> true | _ -> false

let rec unify_fails t1 t2 =
  match t1, t2 with
  | Func _, Set _ -> true
  | Set _, Func _ -> true
  | Ref (_,t,_), Func _ -> unify_fails t t2
  | Ref (_,t,_), Set _  -> unify_fails t t2
  | Func _, Ref (_,t,_) -> unify_fails t1 t
  | Set _,  Ref (_,t,_) -> unify_fails t1 t
  | (Set _| Func _), (Int|Bool|Str|Top) -> true
  | (Int|Bool|Str|Top), (Set _| Func _) -> true
  | Ref (_,a,_), ((Int|Bool|Str) as b)
  | ((Int|Bool|Str) as b), Ref (_,a,_)
  | Ref (_,a,_), (Top as b)
  | (Top as b), Ref (_,a,_)
			-> not (eq a b) && not (is_tyvar a)
  | TyVar _, _ -> false
  | _, TyVar _ -> false
  | Rec _, (Set _ | Func _)
  | (Set _ | Func _), Rec _
      -> true
  | Int, Bool
  | Bool, Int
  | Int, Str
  | Str, Int
  | Str, Bool
  | Bool, Str
      -> true
  | _ ->
      false


let lookup_id cx n =
  assert (n > 0 && n <= length cx) ;
  hyp_name (nth cx (n - 1))


(** Type normal form *)
let rec simplify t =
  (* let is_opaque e = match e.core with Opaque _ -> true | _ -> false in *)
  match t with
  | Set t ->
      Set (simplify t)
  | Func (x,t1,t2) ->
      Func (x, simplify t1, simplify t2)
  | Ref (x, tt, r) ->
      let tt = simplify tt in
      begin match tt, r with
      | Ref (_,_,Ex _), Ex (_,{core = Internal B.TRUE}) ->
          tt
      | Ref (_,t,Ex (cx,e)), Ex (cx',e') ->                                   (** [cx] and [cx'] should be the same, ideally *)
          let ex = Apply (Internal B.Conj |> noprops, [e ; e']) |> noprops in
          Ref (x, t, Ex (cx,ex)) |> simplify
      | _, Ex (cx,e) ->
          let e = Smt.flatten_disj e in
          let e = Smt.flatten_conj e in
          Ref (x, tt, Ex (cx,e))
      | _ ->
          Ref (x, tt, r)
      end
  (* | Ref (x', (Ref (_,t,Ph (_,p))), Ex (cx',e')) ->
      (** FIX ss missing ; cx *)
      let ex = Apply (Internal B.Conj |> noprops, [Opaque p |> noprops ; e']) |> noprops in
      Ref (x',t, Ex (cx',ex)) |> simplify    (** FIX cx *) *)
  (* | TySubst (ss,t) ->
      (* Util.eprintf "!! simp : %a" pp (TySubst (ss,t)); *)
      (* Printf.eprintf "-- free_vars : %s\n" (String.concat "," (expr_fv t)); *)
      let t = simplify t in
      (* let ss = Smt.remove_repeated ss in *)
      begin match ss,t with
      | [],_ ->
          t
      | ss, TySubst (ss',t) ->
          TySubst (ss @ ss',t) |> simplify
      | (v,_,_,_) as s :: ss, Ref (x,t,Ph (ss',p))
        when not (mem v (dom_ss ss')) ->
          assert (v <> x);
          TySubst (ss, Ref (x,t, Ph (s::ss',p))) |> simplify
      | ss, Ref (x,t,Ex (cx,e)) ->
          let cx,e = add_exp_substs cx e ss in
          Ref (x,t, Ex (cx,e)) |> simplify
      | ss, Set t ->
          Set (TySubst (ss,t) |> simplify)
      | _, (Int|Bool|Str) ->
          t
      | _ ->
          TySubst (ss,t)
      end *)
  | Rec rs ->
      Rec (map (fun (h,t) -> (h, simplify t)) rs)
  | Rec_dot (t, h) ->
      let t = simplify t in
      begin match t with
      (** Rec_dot (Rec [h_i -> t_i], h) = t_i  when h = h_i *)
      | Rec rs ->
          begin try
            let _,t = List.find (fun (f,t) -> f = h) rs in
            t |> simplify
          with _ -> Rec_dot (Rec rs, h)
          end
      | t -> Rec_dot (t, h)
      end
  | TyPlus ts ->
      let ts = map simplify ts in
      begin match ts with
      | [] -> TyPlus []
      | [t] -> t
      | [t1 ; t2] when eq t1 t2 -> t1
      | [Ref (x, t1, Ex (cx, _)) ; Ref (y, t2, Ex (cx', {core = Internal B.TRUE}))]
      | [Ref (x, t1, Ex (cx, {core = Internal B.TRUE})) ; Ref (y, t2, Ex (cx', _))]
          when eq t1 t2 ->
          Ref (x, t1, Ex (cx, Internal B.TRUE %% []))
      | [Ref (x, t1, Ex (cx, e1)) ; Ref (_, t2, Ex (_, e2))] when eq t1 t2 ->
          Ref (x, t1, Ex (cx, List (Or, [e1 ; e2]) %% []))
      | [Ref (x, t1, r) ; t2] when eq t1 t2 -> t2
      | [t2 ; Ref (x, t1, r)] when eq t1 t2 -> t2
      | [Tbase t1 ; t2] when eq t1 t2 -> Tbase t1
      | [t2 ; Tbase t1] when eq t1 t2 -> Tbase t1
      | [Set t1 ; Set t2] ->
          Set (TyPlus [t1;t2])
      | [Func (x,t1,t2) ; Func (y,t3,t4)] when eq t1 t3 ->
          Func (x,t1, TyPlus [t2;t4])
      | _ ->
        begin try
          let get_ref_data = function Ref (x, t, Ex (cx, ex)) -> (x,t,cx,ex) | _ -> raise Not_found in
          let ts = map get_ref_data ts in
          let bs = map (fun (x,t,cx,ex) -> t) ts in
          if (for_all (eq (List.hd bs)) (List.tl bs)) then () else raise Not_found ;
          let es = map (fun (x,t,cx,ex) -> ex) ts |> List.rev in
          let x, b, cx = match List.hd ts with (x,t,cx,ex) -> x, t, cx in
          Ref (x, b, Ex (cx, List (Or, es) %% []))
        with _ ->
          TyPlus ts
        end
      end
  | TyTimes ts ->
      let ts = map simplify ts in
      begin match ts with
      | [t] -> t
      | [t1 ; t2] when eq t1 t2 -> t1
      | [Ref (x, t1, Ex (cx, e1)) ; Ref (y, t2, Ex (cx', e2))] when eq t1 t2 ->
          Ref (x, t1, Ex (cx, List (And, [e1 ; e2]) %% []))
      | [Ref (x, t1, r) ; t2] when eq t1 t2 -> Ref (x, t1, r)
      | [t2 ; Ref (x, t1, r)] when eq t1 t2 -> Ref (x, t1, r)
      | [Set t1 ; Set t2] ->
          Set (TyTimes [t1;t2])
      | [Func (x,t1,t2) ; Func (y,t3,t4)] when eq t1 t3 ->
          Func (x,t1, TyTimes [t2;t4])
      | _ ->
        TyTimes ts
      end
  | Tbase t ->
      let t = simplify t in
      begin match t with
      | Ref (_,t,_) -> t
      | Func (x,t1,t2) -> Func ("",Tbase t1,Tbase t2)
      | Set t -> Set (Tbase t)
      | t when is_atomic_type t -> t
      | Rec rs -> Rec (map (fun (h,t) -> (h, Tbase t)) rs)
      | TyVar (_,a) -> Tbase (TyVar ([],a))
      | _ -> Tbase t
      end
  | Tdom t ->
      let t = simplify t in
      begin match t with
      | Func (_,t1,t2) -> t1
      (* | TySubst (ss,t) -> TySubst (ss, Tdom t) *)
      | _ -> Tdom t
      end
  | Tcod t ->
      let t = simplify t in
      begin match t with
      | Func (_,t1,t2) -> t2
      (* | TySubst (ss,t) -> TySubst (ss, Tcod t) *)
      | _ -> Tcod t
      end
  | t -> t

let rec base_to_ref = function
  | t when is_atomic_type t -> mk_ref t
  | Top as t -> mk_ref t
  | Set t -> Set (base_to_ref t)
  | Ref (x,t,Ph (ss,p)) -> Ref (x,t,Ph ((base_to_ref_ss ss), p))
  | Func (x,t1,t2) -> Func (x, base_to_ref t1, base_to_ref t2)
  (* | TySubst (ss,t) -> TySubst (base_to_ref_ss ss, base_to_ref t) *)
  | Rec rs -> Rec (map (fun (h,t) -> (h, base_to_ref t)) rs)
  | Rec_dot (t,h) -> Rec_dot (base_to_ref t,h)
  | TyPlus ts -> TyPlus (map base_to_ref ts)
  | TyTimes ts -> TyTimes (map base_to_ref ts)
  | Tbase t -> Tbase (base_to_ref t)
  | Tdom t -> Tdom (base_to_ref t)
  | Tcod t -> Tcod (base_to_ref t)
  | t -> t
and base_to_ref_ss ss = map (fun (v,cx,e,t) -> v,cx,e,base_to_ref t) ss

let rec ref_to_base = function
  | Ref (_,t,Ex(_,{core = Internal B.TRUE})) -> t
  | Ref (x,t,Ph (ss,p)) -> Ref (x,t,Ph ((ref_to_base_ss ss), p))
  | t when is_atomic_type t -> t
  | Top as t -> t
  | Set t -> Set (ref_to_base t)
  | Func (x,t1,t2) -> Func (x, ref_to_base t1, ref_to_base t2)
  (* | TySubst (ss,t) -> TySubst (ref_to_base_ss ss, ref_to_base t) *)
  | Rec rs -> Rec (map (fun (h,t) -> (h, ref_to_base t)) rs)
  | Rec_dot (t,h) -> Rec_dot (ref_to_base t,h)
  | TyPlus ts -> TyPlus (map ref_to_base ts)
  | TyTimes ts -> TyTimes (map ref_to_base ts)
  | Tbase t -> Tbase (ref_to_base t)
  | Tdom t -> Tdom (ref_to_base t)
  | Tcod t -> Tcod (ref_to_base t)
  | t -> t
and ref_to_base_ss ss = map (fun (v,cx,e,t) -> v,cx,e,ref_to_base t) ss


(****************************************************************************)


(** Typing propositions (only for _ground_ types).
    From assignment [x : t], it constructs the typing proposition [x \in t'].
  		[[x : t]] == x \in t'
    It returns:
      [t']
      [cx']
      [x \in t']
    *)
let rec to_predtyp cx (x:expr) t =
(* Util.eprintf "!! to_predtyp %a:%a" (print_prop ()) x pp t; *)
  let mk x = noprops x in
  let app op x y = Apply (Internal op |> mk, [x ; y]) |> mk in
  let app1 op x = Apply (Internal op |> mk, [x]) |> mk in
  let mem x y = app B.Mem x y in
  let sh1 e = app_expr (shift 1) e in
  let bmp n e = app_expr (bump (shift n)) e in
  let quant q h dom ex =
    let dom = match dom with
    | Some d ->
      (* let t = TLAtype.base (typpbot d) in *)
      (* let h = assign h boundvar () in *)
        [h |> mk (* <<< Some t *), Unknown, Domain d]
    | None -> [h |> mk, Unknown, No_domain]
    in
    (* let ex = app_expr (bump (shift 1)) ex in *)
    Quant (q, dom, ex) |> mk in
  let forall ?dom id ex = quant Forall id dom ex in
  let lAnd es = List (And, es) |> mk in
  let ix1 = (Ix 1 |> mk) in
  (* let ix2 = (Ix 2 |> mk) in *)
  match t with
  | TyAtom t' ->
			TyAtom t', cx, Apply (Opaque t' |> mk, [x]) |> mk
	(** [[x : a]] == a(x) *)
	| TyVar ([],a) ->                   																				(** this case represent atomic types *)
      TyVar ([],a), cx, Apply (Opaque a |> mk, [x]) |> mk
  | TyVar (ss,a) ->
      TyVar (ss,a), cx, Apply (Opaque a |> mk, [x]) |> mk        (** FIX *)
  | Top ->
      t, cx, Internal B.TRUE |> mk
	(** [[x : Int]] == x \in Int *)
  | Int ->
      t, cx, mem x (Internal B.Int |> mk)
	(** [[x : Int]] == x \in BOOLEAN *)
  | Bool ->
      t, cx, mem x (Internal B.BOOLEAN |> mk)
  | Str ->
      t, cx, mem x (Internal B.STRING |> mk)
	(** [[x : Set t]] == \A z \in x : [[z : t]] *)
  | Set t ->
      let z = Smt.fresh_name () in
      let t,cx,ex = to_predtyp cx ix1 t in
      (* let ex = app_expr (bump (shift 1)) ex in *)
      t, cx, forall ~dom:x z (sh1 ex)
	(** [[x : (y:t1) -> t2]] == /\ x = [y \in DOMAIN x |-> x[y]]
	 														/\ \A y : y \in DOMAIN x <=> [[y : t1]]
															/\ \A y : [[y : t1]] => [[x[y] : t2]] *)
  | Func (y,t1,t2) ->
      let b1,cx1,p1 = to_predtyp cx ix1 t1 in
      (* let b2,cx2,p2 = to_predtyp cx ix2 t2 in *)
      let b3,cx3,p3 = to_predtyp cx1 (FcnApp (x, [ix1]) %% []) t2 in
      Func ("",b1,b3), cx, lAnd [
			  app B.Eq x (Fcn ([y %% [], Unknown, Domain (app1 B.DOMAIN x)],
					FcnApp (sh1 x, [ix1]) %% []) %% []) ;
        forall y (app B.Equiv (mem ix1 (app1 B.DOMAIN x)) (bmp 1 p1)) ;
        forall y (app B.Implies (bmp 1 p1) (bmp 1 p3))
        (* forall y (forall z (app B.Implies
          (app B.Conj (bmp 2 p1) (bmp 2 p2))
          (bmp 2 p3))) *)
				]
  | Ref (_,t,Ex (cx,e)) ->
      let t,cx,p = to_predtyp cx x t in
      t, cx, lAnd [p ; app_expr (scons x (shift 0)) e]
  | Ref (_,_,Ph _)
    ->
      (** CHECK. this should fail *)
      t,cx,Internal B.TRUE |> mk
  | Rec rs ->
      (** CHECK *)
      let ex = lAnd (map (fun (h,t) ->
        let _,_,ex = to_predtyp cx (Dot (x,h) |> mk) t in
        ex
        ) rs) in
      t,cx,ex
  | Rec_dot (t,h) ->
      (** CHECK *)
      t,cx,Internal B.TRUE |> mk
  | TyPlus ts ->
      let ts, es = fold_left
        begin fun (ts,es) t ->
        let t1,cx1,e1 = to_predtyp cx ix1 t in
        (t1::ts, e1::es)
        end ([],[]) ts
      in
      TyPlus ts, cx, (List (Or, map sh1 es) %% [])
  | TyTimes ts ->
      let ts, es = fold_left
        begin fun (ts,es) t ->
        let t1,cx1,e1 = to_predtyp cx ix1 t in
        (t1::ts, e1::es)
        end ([],[]) ts
      in
      TyTimes ts, cx, lAnd (map sh1 es)
  | Tbase t ->
      t,cx,Internal B.TRUE |> mk
  | Tdom t ->
      t,cx,Internal B.TRUE |> mk
  | Tcod t ->
      t,cx,Internal B.TRUE |> mk

(****************************************************************************)

let lookup_type scx n =
  match Deque.nth ~backwards:true scx (n - 1) with
  | Some h ->
      begin match h.core with
      | Fresh (nm, _, _, _)
      | Flex nm
      (* | Defn ({core = Operator (nm, _) | Instance (nm, _)
                      | Bpragma(nm,_,_) | Recursive (nm, _)},
              _, _, _) *)
        -> optype nm
      | _ -> None
      end
  | _ -> None

let rec lookup_type_by_id scx id =
  match Deque.rear scx with
  | Some (cx,h) ->
      begin match h.core with
      | Flex nm | Fresh (nm, _, _, _) when nm.core = id ->
          optype nm
      | _ ->
          lookup_type_by_id cx id
      end
  | None -> None

let reduce_func tf ts =
  begin match tf, ts with
  | Func (_,a,b), [a'] when eq a a' -> b
  | _ -> Top
  end

let rec get_type scx e : t option =
(* Util.eprintf "\tget_type \t%a" (print_prop ()) (opaque cx e) ; *)
  (* let _is_int e = get_type scx e = Int in *)
  let oget scx e = Option.default Top (get_type scx e) in
  match e.core with
  | Ix n ->
      lookup_type scx n
  | Opaque id ->
      lookup_type_by_id scx id
  | Apply ({core = Opaque "tla__fcnapp_i"}, _) ->
      Some Int
  | Apply ({core = Internal op}, es) ->
      begin match op, es with
      | B.Conj, _ | B.Disj, _ | B.Implies, _ | B.Equiv, _ | B.Neg, _ | B.Eq, _ | B.Mem, _
      | B.Neq, _ | B.Notmem, _ | B.Subseteq, _
      | B.Lt, _ | B.Lteq, _ | B.Gt, _ | B.Gteq, _ ->
          Some Bool
      | B.Plus, _ | B.Minus, _ | B.Times, _ | B.Ratio, _
      | B.Quotient, _ | B.Remainder, _ | B.Exp, _ | B.Uminus, _ ->
          if for_all (_is_int scx) es then Some Int else None
      | B.Range, _ ->
          if for_all (_is_int scx) es then Some (Set Int) else None
      | B.Prime, [ex] ->
          get_type scx ex
      | B.DOMAIN, [f] ->
          begin match get_type scx f with
          | Some (Func (_,t1,_)) -> Some (Set t1)
          | _ -> None
          end
      | (B.Cup | B.Cap | B.Setminus), [e1 ; e2] ->
          begin match get_type scx e1, get_type scx e2 with
          | Some t1, Some t2 when eq t1 t2 -> Some t1
          | _ -> None
          end
      | B.SUBSET, [ex] ->
          begin match get_type scx ex with
          | Some t -> Some (Set t)
          | None -> None
          end
      | B.UNION, [ex] ->
          begin match get_type scx ex with
          | Some (Set t) -> Some t
          | _ -> None
          end
      (* | B.Len, _ -> Int *)      (*** Bug!! *)
      (* | B.Head, ex :: _ -> get_type scx ex
      | B.Tail, _ :: es -> Tup (map (get_type scx) es)
      | B.Seq, _ -> Set (Tup [])
      | B.BSeq, _ -> Tup []
      | B.Cat, _ -> Tup []
      | B.Append, _ -> Tup []
      | B.SubSeq, _ -> Tup []
      | B.SelectSeq, _ -> Tup [] *)

      | B.Unprimable, [ex] ->
          get_type scx ex
      | _ ->
          None
          (* Util.bug "[SMT] get_type: not supported Apply Internal" *)
      end
  | Apply (f, es)
  | FcnApp (f, es) ->
      (* let t = get_type scx f in
      let ts = map (get_type scx) es in
      let ts' = try Some (map Option.get ts) with _ -> None in
      begin match t, ts' with
      | Some t, Some ts -> Some (reduce_func t ts)
      | _ -> None
      end *)
      None
  | SetEnum [] ->
      Some (Set Top)
  | SetEnum es ->
      let ts = map (get_type scx) es in
      begin try
        let ts = map Option.get ts in
        (if for_all (fun t' -> eq (hd ts) t') (tl ts) then () else raise Not_found) ;
        Some (Set (hd ts))
      with _ -> None end
  | Internal B.TRUE
  | Internal B.FALSE    -> Some Bool
  | Internal B.Infinity -> Some Int
  | List _
  | Quant _            -> Some Bool
  | Internal B.BOOLEAN -> Some (Set Bool)
  | Internal B.STRING  -> Some (Set Str)
  | String _           -> Some Str
  | Num _              -> Some Int
  | Internal B.Nat
  | Internal B.Int     -> Some (Set Int)
  (* | Tuple es       -> Tup (map (get_type scx) es) *)
  | Tuple [] -> Some (Func ("",Int,Top))
  | Tuple es ->
      let t = oget scx (hd es) in
      Some (Func ("",Int, t))
  | Record rs ->
      Some (Rec (map (fun (h,e) ->
        (h, oget scx e)
      ) rs))
  | Dot (r,h) ->
      let t = simplify (Rec_dot (oget scx r, h)) in
      begin match t with
      | Rec_dot _ -> Some Top
      | _ -> Some t
      end
  | If (_, t, u) ->
      begin match get_type scx t, get_type scx u with
      | Some tt, Some tu -> Some tt
      | _ -> None
      end
  | Sequent _ ->
      Some Bool
  | _ ->
      None
and _is_int scx e =
  begin match get_type scx e with
  | Some Int -> true
  | Some (Ref (_,Int,_)) -> true
  | _ -> false
  end


(** TOFIX: incomplete: Apply, FcnApp, Choose, ... *)
let rec is_int scx e =
  match e.core with
  | Num (_,"") -> true
  | Ix _ -> _is_int scx e
      (* lookup_type scx n = Some Int *)
      (* assert (n > 0 && n <= Ctx.length cx) ;
      let id = Ctx.string_of_ident (fst (Ctx.index cx n)) in
      id       *)
  | Apply ({core = Internal op}, [e1 ; e2]) ->
      begin match op with
      | B.Plus | B.Minus | B.Times | B.Exp ->
         is_int scx e1 && is_int scx e2
      (** This works with the encoding hack as IFs, because the condition [e1 \in Int /\ e2 \in Int /\ 0 < e2] is an implicit condition. *)
      | B.Remainder | B.Quotient ->
         is_int scx e1 && is_int scx e2
      | _ ->
        false
      end
  | Apply ({core = Internal B.Uminus}, [ex]) ->
      is_int scx ex
  | Apply ({core = Internal B.Len}, _) -> true
  | If (_, t, f) ->
      is_int scx t && is_int scx f
  | _ ->
    false

(** This function does not require any context *)
let rec is_hard_bool e =
(* Util.eprintf "\tget_type \t%a" (print_prop ()) (opaque cx e) ; *)
  match e.core with
  | Internal B.TRUE | Internal B.FALSE -> true
  | List _ | Quant _ | Sequent _ -> true
  | Apply ({core = Internal op}, _) ->
      begin match op with
      | B.Conj | B.Disj | B.Implies | B.Equiv | B.Neg | B.Eq | B.Mem
      | B.Neq | B.Notmem | B.Subseteq
      | B.Lt | B.Lteq | B.Gt | B.Gteq ->
          true
      | _ ->
          false
      end
  | Apply ({core = Opaque "boolify"}, _) -> true
  | Apply ({core = Opaque "tla__isAFcn"}, _) -> true
  | If (_, t, f) ->
      is_hard_bool t && is_hard_bool f
  (* | Choose () *)
  | _ ->
      false

(** TOFIX: incomplete *)
let rec is_bool scx e =
(* Util.eprintf "\tget_type \t%a" (print_prop ()) (opaque cx e) ; *)
  is_hard_bool e ||
  match e.core with
  | Ix n ->
      lookup_type scx n = Some Bool
  | Opaque id ->
      lookup_type_by_id scx id = Some Bool
  (* | Apply ({core = Opaque "boolify"}, _) -> true *)
  (* | Apply ({core = Internal B.Prime}, _) -> *)
  (* | Apply (op, es) ->  *)
  (* | FcnApp (f, es) -> *)
  | If (_, t, f) ->
      is_bool scx t && is_bool scx f
  (* | Choose () *)
  | _ ->
      false
