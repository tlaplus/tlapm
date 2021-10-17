(************************************************************************
*
*  typ_e.ml
*
*
*  Created by Hernán Vanzetto on 23 Oct 2013.
Copyright (c) 2013  INRIA and Microsoft Corporation
*
************************************************************************)

open Ext
open Property

open Expr.T
open Expr.Subst
open Expr.Visit

open List

module SSet = Smtcommons.SSet
module SMap = Smtcommons.SMap

open Typ_t
module T = Typ_t
module Dq = Deque

(****************************************************************************)

let hyp_optype h =
    match h.core with
    | Fresh (nm, _, _, _)
    | Flex nm
    | Defn ({core=Operator (nm, _)
            | Instance (nm, _)
            | Bpragma(nm, _, _)
            | Recursive (nm, _)},
            _, _, _) ->
        optype nm
    | Fact (_, _, _) ->
        None

(****************************************************************************)
(* Equivalence classes of type variables                                    *)
(****************************************************************************)

let type_equiv = ref SMap.empty

let type_equiv_singleton a =
    type_equiv := SMap.add
        a (SSet.singleton a) !type_equiv

let type_equiv_find a = SMap.fold
    begin fun k set r ->
        if k = a || SSet.mem a set
            then Some (k, set)
            else r
    end
    !type_equiv None

let type_equiv_union a b =
    let k1, s1 = Option.default
        (a, SSet.singleton a) (type_equiv_find a) in
    let k2, s2 = Option.default
        (b, SSet.singleton b) (type_equiv_find b) in
    type_equiv := SMap.add k1
        (SSet.union s1 s2) (SMap.remove k2 !type_equiv)

(** add [a] to the class of [b] *)
let add_type_equiv b a =
    let id, set = Option.default
        (a, SSet.empty) (type_equiv_find b) in
    type_equiv := SMap.add
        id (SSet.add a set) !type_equiv

let type_equiv_pp v = SMap.iter
    begin fun k set ->
        Smtcommons.ifprint
            v "  %s |--> { %s }" k
            (String.concat "," (SSet.elements set))
    end
    !type_equiv

(****************************************************************************)
(* Type assignments                                                         *)
(****************************************************************************)

(** Mapping
[TyVar] --> [cx * expr] option *
    [bool] * [T.t] option
(context |- expression, is_bounded, type)
*)
let tyvar_assignment = ref SMap.empty

let ctr_types = ref 0
let fresh_tyvar ?id (cx, e) =
    (*
    let a = Option.default
        ("a" ^ string_of_int
         (incr ctr_types; !ctr_types)) id in
    *)
    (* let a = Option.default z id in *)
    let z = "a" ^ string_of_int
        (incr ctr_types; !ctr_types) in
    let a, bvar = match id with
          None -> z, false
        | Some id -> (z ^ id), true in
    type_equiv_singleton a;
    tyvar_assignment := SMap.add
        a (Some(cx, e), bvar, None)
        !tyvar_assignment;
    a

(****************************************************************************)
(* Typing contexts                                                          *)
(****************************************************************************)

(* type t = ((string * T.t) option) Dq.dq *)
type t = (hyp * T.t option) Dq.dq

let empty = Dq.empty

(* let ( $$ ) env (x, t) = Dq.cons (Some (x, t)) env *)
let ( $$ ) env (h, ot) = Dq.snoc env (h, ot)
let ( $! ) e1 e2 = Dq.append e1 e2

(* let _mk_hyp v = Flex (v %% []) %% [] *)
let _mk_hyp_fresh v = Fresh (
    v %% [],
    Shape_expr,
    Constant,
    Unbounded) %% []
let _mk_hyp_defn v ar = Defn (
    Operator (
        v %% [],
        Internal Builtin.TRUE %% []) %% [],
    User, Visible, Local) %% []

let adj env (v, t) = env $$ (_mk_hyp_fresh v, Some t)

let adj_none env v = env $$ (_mk_hyp_fresh v, None)

let rec adjs env = function
    | [] -> env
    | xt :: xts ->
        adjs (adj env xt) xts

(** mk_from_hyp *)
let adj_hyp env h =
    let mk_a id = fresh_tyvar
        ~id:id ([], Opaque ("hyp-" ^ id) %% []) in
    match h.core with
    | Fresh (nm, shp, lc, dom) ->
        let a = mk_a nm.core in
        (*
        Util.eprintf
            "-- E.mk : %s -> \\%s [fresh]"
            nm.core a;
        *)
        (env $$ (h, Some (TyVar ([], a))), Some a)
    | Flex nm ->
        let a = mk_a nm.core in
        (*
        Util.eprintf
            "-- E.mk : %s -> \\%s [flex]"
            nm.core a;
        *)
        (env $$ (h, Some (TyVar ([], a))), Some a)
    | Defn ({core=Operator (nm, _)}, _, Visible, _) ->
        let a = mk_a nm.core in
        (*
        Util.eprintf
            "-- E.mk : %s -> \\%s [defn]"
            nm.core a;
        *)
        (env $$ (h, Some (TyVar ([], a))), Some a)
    | _ ->
        (*
        Util.eprintf
            "-- E.mk : ---";
        *)
        (env $$ (h, None), None)

let rec adj_hyps env hs = match Dq.front hs with
    | None -> (env, [])
    | Some (h, hs) ->
        let (env, ao) = adj_hyp env h in
        let (env, ass) = adj_hyps env hs in
        let ass = match ao with
              None -> ass
            | Some a -> ass @ [a] in
        (env, ass)

(** Make environment from
(free) variables [vs]
*)
let mk vs =
    let ass = map
        (fun v -> fresh_tyvar
            ~id:v
            ([], Opaque ("fv-" ^ v) %% []))
            vs in
    let env = fold_left2
        (fun env v a -> adj
            env (v, TyVar ([], a)))
        empty vs ass in
    (env, ass)

let to_list (env:t) =
    (* List.fold_left
        (fun r -> function
              None -> r
            | Some (x, t) -> (x, t) :: r)
        []
    *)
    (Dq.to_list env)

let _types (env:t) =
    List.fold_left
        (fun r -> function
              _, None -> r
            | h, Some t -> t :: r)
        []
        (Dq.to_list env)

let find x env =
    let env = Dq.map
        (fun _ (h, ot) -> hyp_name h, ot)
        env in
    try
        Option.get (assoc x (Dq.to_list env))
    with _ ->
        begin
        Smtcommons.ifprint 1
            "Type for %s not found in environment." x;
        raise Typeinf_failed
        end

let eq
        (e1:t)
        (e2:t) :
            bool =
    let e1 = Dq.to_list e1 in
    let e2 = Dq.to_list e2 in
    begin
    try
        for_all2
            begin fun (h1, o1) (h2, o2) ->
                Expr.Eq.hyp h1 h2 &&
                match o1, o2 with
                | Some t, Some t' -> T.eq t t'
                | None, None -> true
                | _ -> false
            end
            e1 e2
    with _ -> false
    end

let subst
        (a:string)
        (t:T.t) env =
    Dq.map
        (fun i -> function
              h, None -> h, None
            | h, Some t' -> h, Some (T.subst a t t'))
        env

let vsubst
        (a:string)
        (b:string)
        env =
    (*
    Dq.map
        (fun i -> function
              h, None -> h, None
            | h, Some t ->
                h,
                Some (
                    (if a = x then b else x),
                    T.vsubst a b t))
        env
    *)
    Dq.map
        (fun i -> function
              h, None -> h, None
            | h, Some t -> h, Some (T.vsubst a b t))
        env  (** CHECK *)

(*
let pp ppf env =
    let pp_print_elem ppf (x, t) = fprintf
        ppf "@[<h>%s:%a@]" x T.pp t in
    fprintf
        ppf "@[<hv>%a@] "
        (pp_print_delimited pp_print_elem)
        env
*)

(** Free type variables *)
let tyvars env =
    List.flatten (List.map T.fv (_types env))

let to_scx env =
    Dq.map
        begin fun i -> function
            | h, None -> h
            | h, Some t -> h
        end
        env

let to_cx env =
    Smtcommons.to_cx (to_scx env)

let simplify env =
    Dq.map
        (fun i -> function
              h, None -> h, None
            | h, Some t -> h, Some (T.simplify t))
        env

let ss_to_env ss = fold_left
    (fun e (v, _, _, t) -> adj e (v, t))
    empty ss

let map f env = Dq.map
      begin fun i -> function
          | h, None -> h, None
          | h, Some t -> h, Some (f t)
      end
      env

(****************************************************************************)
(* Typing contexts                                                          *)
(****************************************************************************)

(* type t = (string * T.t) list

let empty = []

let ( $$ ) env (x, t) = (x, t) :: env
let ( $! ) e1 e2 = e1 @ e2

let mk vs =
    let ass = map
        (fun v -> fresh_tyvar
            ~id:v ([], Opaque ("fv-" ^ v) %% []))
        vs in
    let env = fold_left2
        (fun env v a -> env $$ (v, TyVar ([], a)))
        empty vs ass in
    (ass, env)

let find x env =
    try
        assoc x env
    with Not_found ->
        failwith (
            "Type for "^x^" not found in environment.")

let eq e1 e2 : bool =
    begin
    try
        for_all2
            (fun (x, t) (x', t') ->
                x = x' &&
                T.eq t t')
            e1 e2
    with _ ->
        false end

let subst
        (a:string)
        (t:T.t)
        env =
    map
        (fun (x, t') -> (x, T.subst a t t'))
        env

let vsubst (a:string) (b:string) env =
    map
        (fun (x, t) ->
            (if a = x then b else x),
            T.vsubst a b t)
        env

(*
let pp ppf env =
    let pp_print_elem ppf (x, t) = fprintf
        ppf "@[<h>%s:%a@]" x T.pp t in
    fprintf
        ppf "@[<hv>%a@] "
        (pp_print_delimited pp_print_elem)
        env
*)

(** Free type variables *)
let tyvars env =
    let xs, ts = split env in
    (* list_minus (flatten (map fv ts)) xs *)
    flatten (map fv ts)

(** returns the types in the range of [vs],
filtered to only type variables *)
let finds env vs =
    fold_left
        (fun r (x, t) ->
            if mem x vs
                then (
                    match t with
                          TyVar (_, a) -> a :: r
                        | _ -> r)
                else r)
        [] env
    (*
    let finds env vs =
        let find v env =
            try
                (match assoc v env with
                  TyVar a -> [a]
                | _ -> [])
            with _ ->
                [] in
    fold_left
        (fun r v -> r @ find v env)
        [] vs
    *)

let to_cx env =
    fold_left
        (fun r (x, t) ->
            T.add_x_ctx x t r)
        [] (List.rev env)

let to_scx env =
    Smtcommons.to_scx (to_cx env)

let simplify env = map
    (fun (x, t) -> (x, T.simplify t))
    env
*)






















(****************************************************************************)

(* open Format *)
let fprintf = Format.fprintf
let pp_print_string = Format.pp_print_string
let pp_print_cut = Format.pp_print_cut
let pp_print_as = Format.pp_print_as
let pp_print_int = Format.pp_print_int
let pp_print_space = Format.pp_print_space
(* open Fmtutil *)
let pp_print_delimited = Fmtutil.pp_print_delimited
let pp_print_with_parens = Fmtutil.pp_print_with_parens
(* open Tla_parser   (** for [fmt_expr] *) *)
module Fu = Tla_parser.Fu

module B = Builtin

let is_eq e =
    match e.core with
    | Apply (
            {core=Internal B.Eq},
            [{core=Ix 1}; _]) -> true
    | _ -> false
(*
let is_setenum e =
    match e.core with
    | List (Or, es)
            when for_all is_eq es ->
        true
    | _ ->
        false
*)

(*
let pp_cx ppf cx =
    let cx = mapi
        (fun i k -> Smtcommons.lookup_id cx (i + 1))
        cx in
    Util.eprintf
        "@[<hov>%a@]"
        (pp_print_delimited pp_print_string) cx
*)

(****************************************************************************)
(** The following functions are an exact copy
of the corresponding functions in [Expr.Fmt]
__except__  for
[fmt_expr:SetSt, Choose],
[fmt_bounds],
[pp_print_chunk] and
[pp_print_hyp]
that were modified to print type
decorations of bounded variables.
Only for debugging.
*)

let pp_print_var ff v = pp_print_string ff v.core

let is_letter c =
  match c with
  | 'A'..'Z' | 'a'..'z' -> true
  | _ -> false
;;

let is_hidden h = match h.core with
  | Defn (_, _, us, _)
  | Fact (_, us, _) -> us = Hidden
  | _ -> false

let rec is_with e = match e.core with
  | Lambda (_, e) -> is_with e
  | Sequent sq -> is_with sq.active
  | With _ -> true
  | _ -> false

let has_with df = match df.core with
  | Operator (_, e) -> is_with e
  | _ -> false

let elide h =
  not (Params.debugging "hidden")
  && begin
    match h.core with
      | Defn (df, wd, us, _) ->
          not (Params.debugging "alldefs")
          && (us = Hidden || has_with df || wd <> User)
      | Fact (e, us, _) ->
          us = Hidden || is_with e
      | _ -> false
  end

(* let p_boolify cond ff doit =
  (if cond then fprintf ff "(boolify ");
  doit () ;
  (if cond then fprintf ff ")") *)

(* let isboo = Property.has ew Smtcommons.boolify_prop in *)
(* let p_boolify cond ff = (if cond then fprintf ff "^bool") *)
      (* (if isboo then "^bool" else "") *)

let rec fmt_expr (cx:Expr.Fmt.ctx) ew = match ew.core with
  | ( Ix _ | Opaque _ | Internal _ ) ->
      fmt_apply cx ew []
  | Lambda (vss, e) ->
      Fu.Big (fun ff -> pp_print_lambda cx ff vss e)
  | Bang (e, sels) ->
      Fu.Atm begin
        fun ff ->
          pp_print_expr cx ff e ;
          pp_print_sels cx ff sels
      end
  | Apply (op, args) ->
      fmt_apply cx op args
  | Sequent sq ->
      Fu.Big (fun ff -> ignore (pp_print_sequent cx ff sq))
  | With (e, m) ->
      if Params.debugging "meth" then
        Fu.Atm begin fun ff ->
          fprintf ff "@[<hov2>(%a (* : %a *))@]"
            (pp_print_expr cx) e
            Method.pp_print_method m
        end
      else fmt_expr cx e
  | If (e, f, g) ->
      Fu.Big begin
        fun ff ->
          fprintf ff
            "@[<hv2>@[<b2>IF@ %a@]@ @[<b2>THEN %a@]@ @[<b2>ELSE %a@]@]"
            (pp_print_expr cx) e
            (pp_print_expr cx) f
            (pp_print_expr cx) g
      end
  | List (Refs, []) ->
      Fu.Atm (fun ff -> pp_print_string ff "TRUE")
  | List (Refs, [e]) ->
      fmt_expr cx e
  | List (q, es) ->
      let qrep = match q with
        | And | Refs -> "/\\"
        | _   -> "\\/" in
      let pp_print_elem ff e =
        fprintf ff "@[<h>%s %a@]" qrep (pp_print_expr cx) e
      in
      Fu.Big begin
        fun ff ->
          fprintf ff "@[<v0>%a@]"
            (pp_print_delimited ~sep:pp_print_cut pp_print_elem) es
      end
  | Let (ds, e) ->
      Fu.Big (fun ff ->
                fprintf ff "@[<hv0>LET @[<v0>" ;
                let cx = pp_print_defns cx ff ds in
                fprintf ff "@]@\nIN  %a@]" (pp_print_expr cx) e)
  | Quant (q, bs, e) ->
      let (ecx, bsf) = fmt_bounds cx bs in
      let rep = match q with
        | Forall -> "\\A"
        | Exists -> "\\E"
      in
      Fu.Big (fun ff ->
                fprintf ff "@[<b3>%s @[<b0>%t@] :@ %a@]"
                  rep bsf (pp_print_expr ecx) e)

  | Tquant (q, vs, e) ->
      let (ecx, vs) = Expr.Fmt.adjs cx vs in
      let rep = match q with
        | Forall -> "\\AA"
        | Exists -> "\\EE"
      in
      Fu.Big (fun ff ->
                fprintf ff "@[<b4>%s @[<b0>%a@] : %a@]"
                  rep
                  (pp_print_delimited pp_print_string) vs
                  (pp_print_expr ecx) e)
  | Choose (v, optdom, e) ->
      let t = optype v in
      let (ecx, v) = Expr.Fmt.adj cx v in
      begin match optdom with
        | Some dom ->
            Fu.Big begin fun ff ->
              fprintf ff "@[<b2>CHOOSE @[<b2>%s%a \\in@ %a@] :@ %a@]"
                v pp_print_optype (ecx, t) (pp_print_expr cx) dom
                (pp_print_expr ecx) e
            end
        | None ->
            Fu.Big begin fun ff ->
              fprintf ff "@[<b2>CHOOSE %s%a :@ %a@]"
                v pp_print_optype (ecx, t) (pp_print_expr ecx) e
            end
      end
  | SetSt (v, dom, e) ->
      let t = optype v in
      let (ecx, v) = Expr.Fmt.adj cx v in
      Fu.Atm (fun ff ->
                fprintf ff "@[<b3>{@[<b2>%s%a \\in@ %a@] :@ %a}@]"
                  v pp_print_optype (ecx, t) (pp_print_expr cx) dom
                  (pp_print_expr ecx) e)
  | SetOf (e, bs) ->
      let (ecx, bsf) = fmt_bounds cx bs in
      Fu.Atm (fun ff ->
                fprintf ff "@[<b3>{%a :@ %t}@]"
                  (pp_print_expr ecx) e bsf)
  | SetEnum es ->
      Fu.Atm begin
        fun ff ->
          fprintf ff "@[<h>{@[<b0>%a@]}@]"
            (pp_print_delimited (pp_print_expr cx)) es
      end
  | Arrow (e, f) ->
      Fu.Atm begin
        fun ff ->
          fprintf ff "@[<b3>[%a ->@ %a]@]"
            (pp_print_expr cx) e
            (pp_print_expr cx) f
      end
  | Fcn (bs, e) ->
      let (ecx, bsf) = fmt_bounds cx bs in
      Fu.Atm (fun ff ->
                fprintf ff "@[<b3>[%t |->@ %a]@]"
                  bsf (pp_print_expr ecx) e)
  | FcnApp (f, es) ->
      let isboo = Property.has ew Smtcommons.boolify_prop in
      Fu.Atm begin
        fun ff ->
          fprintf ff "@[<h>%a@[<b1>[%a]@]@]%s"
            (pp_print_expr cx) f
            (pp_print_delimited (pp_print_expr cx)) es
            (if isboo then "^bool" else "")
      end
  | Product [e] ->
      fmt_expr cx e
  | Product (e :: es) ->
      Fu.Op begin
        "\\X",
        (fun ff -> fprintf ff "@ \\X "),
        (10, 13),
        Fu.Infix (Fu.Right, fmt_expr cx e, fmt_expr cx (Product es @@ ew))
      end
  | Product _ -> Errors.bug ~at:ew "Expr.Fmt.fmt_expr: PRODUCT []"
  | Tuple es ->
      Fu.Atm begin
        fun ff ->
          fprintf ff "@[<b2><<%a>>@]"
            (pp_print_delimited (pp_print_expr cx)) es
      end
  | Rect fs ->
      Fu.Atm (fun ff ->
                fprintf ff "@[<b1>[%a]@]"
                  (pp_print_delimited
                     (fun ff (v, e) ->
                        fprintf ff "@[<h>%s : %a@]"
                            v (pp_print_expr cx) e)) fs)
  | Record fs ->
      Fu.Atm (fun ff ->
               fprintf ff "@[<b1>[%a]@]"
                  (pp_print_delimited
                     (fun ff (v, e) ->
                        fprintf ff "@[<h>%s |-> %a@]"
                            v (pp_print_expr cx) e)) fs)
  | Except (e, xs) ->
      Fu.Atm (fun ff ->
                fprintf ff "@[<b3>[%a EXCEPT@ @[<v0>%a@]]@]"
                  (pp_print_expr cx) e
                  (pp_print_delimited
                     (fun ff (tr, e) ->
                        fprintf ff "!@[<h>%a = %a@]"
                          (pp_print_delimited ~sep:(fun ff () -> ())
                             (fun ff -> function
                                | Except_dot s ->
                                    fprintf ff ".%s" s
                                | Except_apply e ->
                                    fprintf ff "[%a]"
                                        (pp_print_expr cx) e))
                          tr
                          (pp_print_expr cx)
                          e))
                  xs)
  | Dot (e, f) ->
      Fu.Op (".",
        (fun ff -> pp_print_string ff "."),
        (16, 16),
        Fu.Infix (
            Fu.Left,
            fmt_expr cx e,
            Fu.Atm (fun ff -> pp_print_string ff f)))
  | Sub (q, e, f) ->
      Fu.Atm (fun ff ->
                fprintf ff "@[<h>%s@[<b2>%a@]%s%a@]"
                  (match q with Box -> "[" | _ -> "<<")
                  (pp_print_expr cx) e
                  (match q with Box -> "]_" | _ -> ">>_")
                  (pp_print_expr cx) f)
  | Tsub (q, e, f) ->
      Fu.Atm (fun ff ->
                fprintf ff "@[<h>%s@[<b2>%a@]%s%a@]"
                  (match q with Box -> "[][" | _ -> "<><<")
                  (pp_print_expr cx) e
                  (match q with Box -> "]_" | _ -> ">>_")
                  (pp_print_expr cx) f)
  | Fair (q, e, f) ->
      Fu.Big (fun ff ->
                fprintf ff "@[<h>%s_%a (%a)@]"
                  (match q with Weak -> "WF" | _ -> "SF")
                  (pp_print_with_parens (pp_print_expr cx)) e
                  (pp_print_expr cx) f)
  | Case (arms, oth) ->
      Fu.Big (fun ff ->
                fprintf ff "@[<v2>CASE %a%a@]"
                  (pp_print_delimited
                     ~sep:(fun ff () -> fprintf ff "@,[] ")
                     (fun ff (e, f) ->
                        fprintf ff "@[<b2>%a ->@ %a@]"
                          (pp_print_expr cx) e
                          (pp_print_expr cx) f))
                  arms
                  (fun ff -> function
                     | None -> ()
                     | Some oth ->
                         fprintf ff "@,[] @[<b2>OTHER ->@ %a@]"
                           (pp_print_expr cx) oth)
                  oth)
  | String s ->
      Fu.Atm (fun ff ->
                fprintf ff "\"%s\"" s)
  | Num (m, "") ->
      Fu.Atm (fun ff -> pp_print_string ff m)
  | Num (m, n) ->
      Fu.Atm (fun ff -> fprintf ff "%s.%s" m n)
  | At _ ->
      Fu.Atm (fun ff -> pp_print_string ff "@")
  | Parens (e, {core=Nlabel (l, []) | Xlabel (l, [])}) -> begin
      let f = fmt_expr cx e in
      match f with
        | Fu.Atm _ | Fu.Big _ ->
            Fu.Atm (fun ff ->
                fprintf ff "%s::%a" l Fu.pp_print_minimal f)
        | _ ->
            Fu.Atm (fun ff ->
                fprintf ff "%s::(%a)" l Fu.pp_print_minimal f)
    end
  | Parens (e, {core=Nlabel (l, xs)}) -> begin
      let fe = fmt_expr cx e in
      let fmt = match fe with
        | Fu.Atm _ ->
            format_of_string "%s(%a)::%a"
        | Fu.Big _ ->
            format_of_string "%s(%a)::(%a)"
        | _ ->
            format_of_string "(%s(%a):: %a)"
      in
      Fu.Atm begin fun ff ->
        fprintf ff fmt
          l (pp_print_delimited pp_print_var) xs
          Fu.pp_print_minimal fe
      end
    end
  | Parens (e, {core=Xlabel (l, xs)}) ->
      let xs = List.map begin
        fun (h, x) ->
          try Ctx.string_of_ident (fst (Ctx.index (snd cx) x)) @@ h
          with _ -> ("¶" ^ string_of_int x) @@ h
      end xs in
      fmt_expr cx (Parens (e, Nlabel (l, xs) @@ e) @@ e)
  | Parens (e, {core=Syntax}) ->
      fmt_expr cx e

and pp_print_bang ff () =
  if Params.debugging "garish" then
    pp_print_as ff 1 "§"
  else
    pp_print_string ff "!"

and pp_print_sels cx ff sels =
  if sels <> [] then pp_print_bang ff () ;
  pp_print_delimited ~sep:pp_print_bang (pp_print_sel cx) ff sels

and pp_print_sel cx ff = function
  | Sel_down ->
      pp_print_string ff ":"
  | Sel_left ->
      pp_print_string ff "<<"
  | Sel_right ->
      pp_print_string ff ">>"
  | Sel_at ->
      pp_print_string ff "@"
  | Sel_num n ->
      pp_print_int ff n
  | Sel_inst args ->
      fprintf ff "@[<b1>(%a)@]"
        (pp_print_delimited (pp_print_expr cx)) args
  | Sel_lab (l, []) ->
      pp_print_string ff l
  | Sel_lab (l, args) ->
      fprintf ff "@[<b2>%s@,@[<b1>(%a)@]@]"
        l (pp_print_delimited (pp_print_expr cx)) args

and pp_print_lambda cx ff vss e =
  let vs = List.map fst vss in
  let (ecx, _) = Expr.Fmt.adjs cx vs in
  fprintf ff "@[<b2>LAMBDA @[<hv0>%a@] :@ %a@]"
    (pp_print_delimited pp_print_vs) vss
    (pp_print_expr ecx) e

and pp_print_vs ff (v, shp) =
  fprintf ff "%s%a" v.core pp_print_shape shp

and pp_print_shape ff = function
  | Shape_expr -> ()
  | Shape_op n ->
      let unds = List.init n (fun _ -> "_") in
      fprintf ff "@[<hov1>(%a)@]"
        (pp_print_delimited pp_print_string) unds

and fmt_apply (hx, vx as cx) op args = match op.core, args with
  | Lambda (vss, e), _ ->
      Fu.Op begin
        " ",
        (fun ff -> pp_print_space ff ()), (20, 20),
        Fu.Infix begin
          Fu.Left,
          Fu.Big (fun ff -> pp_print_lambda cx ff vss e),
          Fu.Atm begin
            fun ff -> fprintf
                ff "(%a)"
                (pp_print_delimited (pp_print_expr cx))
                args
          end
        end
      end
  | Bang _, [] ->
      fmt_expr cx op
  | Bang _, _ ->
      Fu.Atm begin
        fun ff ->
          fprintf ff "@[<b2>%a@[<b1>(%a)@]@]"
            (pp_print_expr cx) op
            (pp_print_delimited (pp_print_expr cx)) args
      end
  | Internal Builtin.Prime, [e] when !Params.notl ->
      Fu.Op begin
        "#$",
        (fun ff -> pp_print_string ff "#$"),
        (15, 15), Fu.Postfix (fmt_expr cx e)
      end
  | Internal (Builtin.Box false), [e] when Params.debugging "temporal" ->
      Fu.Atm (fun ff -> fprintf ff "[](%a)" (pp_print_expr cx) e)
  | Internal (Builtin.Box false), [e]
  | Internal Builtin.Unprimable, [e] ->
      fmt_expr cx e
  | Internal Builtin.Irregular, [e] ->
      Fu.Atm begin
        fun ff ->
          fprintf ff "@[<h>@<1>%s%a@<1>%s@]"
            "<[" (pp_print_expr cx) e "]>"
      end
  | _ ->
      let top = match op.core with
        | Ix n ->
            let id =
              if n < 0 then "#$$" ^ string_of_int (abs n)
              else if n = 0 then "#$0"
              else if n <= Ctx.length vx then
                Ctx.string_of_ident (fst (Ctx.index vx n))
              else if n - Ctx.length vx <= Deque.size hx then
                hyp_name (
                    Option.get (
                        Deque.nth
                            ~backwards:true
                            hx (n - Ctx.length vx - 1)))
              else "#$" ^ string_of_int n
            in
            let top = Optable.lookup id in
            if Params.debugging "ix" then
              {top with Optable.name=
                  top.Optable.name ^ "#$" ^ string_of_int (abs n)}
            else top
        | Opaque s ->
            let top = Optable.lookup s in
            { top with Optable.name = "?" ^ top.Optable.name }
        | Internal b ->
            Optable.standard_form b
        | _ ->
            Util.eprintf ~at:op
              "Cannot print this (con: %d):@\n  @[%a@]@."
              (Property.unsafe_con op)
              (pp_print_expr cx) op ;
            failwith "impossible"
      in
      begin
        if List.length args = 0 then
          Fu.Atm (fun ff -> pp_print_string ff top.Optable.name)
        else match top.Optable.fix with
          | Optable.Nonfix ->
              Fu.Atm begin
                fun ff ->
                  fprintf ff "@[<b2>%s@[<b1>(%a)@]@]"
                    top.Optable.name
                    (pp_print_delimited (pp_print_expr cx)) args
              end
          | Optable.Prefix when List.length args = 1 ->
              let n = top.Optable.name in
              let fmt =
                if is_letter n.[String.length n - 1]
                then format_of_string "%s@ "
                else format_of_string "%s"
              in
              Fu.Op begin
                top.Optable.name,
               (fun ff -> fprintf ff fmt top.Optable.name),
               top.Optable.prec,
               Fu.Prefix (fmt_expr cx (List.hd args))
             end
          | Optable.Postfix when List.length args = 1 ->
              Fu.Op begin
                top.Optable.name,
                (fun ff -> fprintf ff "%s" top.Optable.name),
                top.Optable.prec,
                Fu.Postfix (fmt_expr cx (List.hd args))
              end
          | Optable.Infix assoc when List.length args = 2 ->
              let fmt =
                if top.Optable.name = ".."
                then format_of_string "%s"
                else format_of_string "@ %s "
              in
              Fu.Op begin
                top.Optable.name,
                (fun ff -> fprintf ff fmt top.Optable.name),
                top.Optable.prec,
                Fu.Infix begin
                  (match assoc with
                     | Optable.Left -> Fu.Left
                     | Optable.Right -> Fu.Right
                     | Optable.Non -> Fu.Non),
                  fmt_expr cx (List.nth args 0),
                  fmt_expr cx (List.nth args 1)
                end (* Fu.Infix *)
              end (* Fu.Op *)
          | _ ->
              Util.eprintf ~at:op "arity mismatch";
              failwith "arity mismatch"
      end

and fmt_bounds cx bs =
  let ts = List.map (fun (v, _, _) -> optype v) bs in
  let (ecx, vs) = extend_bounds cx bs in
  let bs = List.map2 (fun (_, k, d) (v, _) -> (v, k, d)) bs vs in
  let bs = List.map2 (fun (v, k, d) t -> (v, t, k, d)) bs ts in
  begin ecx, fun ff -> match bs with
     | [] -> assert false
     | (v, t, k, d) :: bs ->
         let chs = ref [] in
         let cch = ref [v, t] in
         let cd = ref d in
         List.iter begin
           fun (v, t, k, d) -> match d with
             | Ditto ->
                 cch := (v, t) :: !cch
             | _ ->
                 chs := (List.rev !cch, !cd) :: !chs ;
                 cch := [v, t] ;
                 cd := d
         end bs ;
         chs := (List.rev !cch, !cd) :: !chs ;
         let bss = List.rev !chs in
         pp_print_delimited (pp_print_chunk cx) ff bss
  end

and pp_print_chunk cx ff (vs, dom) =
  let pp_print_var_type ff (v, t) = fprintf
    ff "%s%a" v pp_print_optype (cx, t) in
  match dom with
    | No_domain ->
        pp_print_delimited pp_print_var_type ff vs
    | Domain dom ->
        fprintf ff "@[<hov0>%a@ \\in %a@]"
          (pp_print_delimited pp_print_var_type) vs
          (pp_print_expr cx) dom
    | Ditto ->
        fprintf ff "@[<hov0>%a@ \\in ??????@]"
          (pp_print_delimited pp_print_var_type) vs

and extend_bound ?(prevdom=None) cx (v, _, dom) =
  let (ecx, v) = Expr.Fmt.adj cx v in
  let dom = match dom with
    | Ditto -> prevdom
    | No_domain -> None
    | Domain d -> Some d
  in
  (ecx, (v, dom))

and extend_bounds ?(prevdom=None) cx = function
  | [] -> (cx, [])
  | b :: bs ->
      let (cx, b) = extend_bound ~prevdom:prevdom cx b in
      let (cx, bs) = extend_bounds ~prevdom:(snd b) cx bs in
      (cx, b :: bs)

and pp_print_bound cx ff (v, e) = match e with
  | None -> pp_print_string ff v
  | Some e ->
      fprintf ff "@[<h>%s \\in %a@]" v (pp_print_expr cx) e

and pp_print_expr cx ff e =
  Fu.pp_print_minimal ff (fmt_expr cx e) ;

and pp_print_defn cx ff d =
  match d.core with
    | Operator (nm, {core=Lambda (vss, e)})
    | Bpragma (nm, {core=Lambda (vss, e)}, _) ->
        let vs = List.map fst vss in
        let (ncx, nm) = Expr.Fmt.adj cx nm in
        let (ecx, _) = Expr.Fmt.adjs cx vs in
        fprintf ff "@[<b2>%s@[<b1>(%a)@] ==@ %a@]"
          nm (pp_print_delimited pp_print_vs) vss
          (pp_print_expr ecx) e ;
        ncx
    | Operator (nm, e)
    | Bpragma (nm, e, _) ->
        let (ncx, nm) = Expr.Fmt.adj cx nm in
        fprintf ff "@[<b2>%s ==@ %a@]"
          nm (pp_print_expr cx) e ;
        ncx
    | Instance (nm, i) ->
        let (ncx, nm) = Expr.Fmt.adj cx nm in
        let (cx, vs) = Expr.Fmt.adjs cx i.inst_args in
        fprintf ff "@[<b2>%a == %a@]"
          (fun ff -> function
             | [] -> pp_print_string ff nm
             | is ->
                 fprintf ff "%s (@[<b0>%a@])"
                   nm (pp_print_delimited pp_print_string) vs)
          i.inst_args
          (pp_print_instance cx) i ;
        ncx
    | Recursive (nm, shp) ->
       let (ncx, nm) = Expr.Fmt.adj cx nm in
       fprintf ff
          "@[<b2>NEW CONSTANT %s%a@]"
          nm pp_print_shape shp;
       ncx

and pp_print_instance cx ff i =
  let pp_print_subst ff (v, e) =
    fprintf ff "@[<b2>%s <- %a@]"
      v.core (pp_print_expr cx) e in
  fprintf ff "@[<b2>INSTANCE %s%a@]"
    i.inst_mod
    (fun ff -> function
       | [] -> ()
       | subs ->
           fprintf ff "@ WITH@ %a"
             (pp_print_delimited pp_print_subst) subs)
    i.inst_sub

and pp_print_defns cx ff = function
  | [] -> cx
  | [d] ->
      pp_print_defn cx ff d
  | d :: ds ->
      let cx = pp_print_defn cx ff d in
      pp_print_cut ff () ;
      pp_print_defns cx ff ds

and pp_print_sequent cx ff sq = match Deque.null sq.context with
  | true ->
      pp_print_expr cx ff sq.active ;
      cx
  | _ ->
      let (cx, chs) =
        Deque.fold_left begin
          fun (cx, chs) h ->
            let ch = (cx, h) in
            let cx = match h.core with
              | Fresh (nm, _, _, _) | Flex nm
              | Defn ({core=Operator (nm, _) | Instance (nm, _)
                            | Bpragma (nm, _, _) | Recursive (nm, _) },
                      _, _, _) ->
                  fst (Expr.Fmt.adj cx nm)
              | Fact (_, _, _) ->
                  Expr.Fmt.bump cx
            in (cx, ch :: chs)
        end (cx, []) sq.context in
      let chs = List.filter
        (fun (cx, h) -> not (elide h))
        (List.rev chs) in
      if List.length chs > 0 then begin
        fprintf ff "@[<v0>ASSUME @[<v0>" ;
        pp_print_delimited begin
          fun ff (cx, h) -> ignore (pp_print_hyp cx ff h)
        end ff chs ;
        fprintf ff "@]@\nPROVE  %a@]" (pp_print_expr cx) sq.active
      end else pp_print_expr cx ff sq.active ;
      cx

and pp_print_hyp cx ff h =
  if Params.debugging "hidden" then begin
    if is_hidden h then fprintf ff "(* hidden *)@\n"
  end ;
  match h.core with
    | Fresh (nm, shp, lc, b) ->
        (* minus hack *)
        let t = optype nm in
        let (ncx, nm) = Expr.Fmt.adj cx nm in
        fprintf ff "NEW %s %s%a%a"
          (match lc with
             | Constant -> "CONSTANT"
             | State -> "STATE"
             | Action -> "ACTION"
             | Temporal -> "TEMPORAL"
             | Unknown -> "UNKNOWN")
          nm pp_print_shape shp pp_print_optype (cx, t);
        (match b with
           | Unbounded
           | Bounded (_, Hidden) -> ()
           | Bounded (b, _) ->
              fprintf ff
              " \\in %a" (pp_print_expr cx) b);
        ncx
    | Flex nm ->
        let t = optype nm in
        let (ncx, nm) = Expr.Fmt.adj cx nm in
        fprintf ff "@[NEW VARIABLE %s%a@]" nm pp_print_optype (cx, t);
        ncx
    | Defn (d, wd, us, _) ->
        if Params.debugging "alldefs" then begin
          fprintf ff begin
            match wd with
              | Builtin -> format_of_string "(* builtin *)@\n"
              | Proof _ -> format_of_string "(* from proof *)@\n"
              | _ -> format_of_string ""
          end
        end ;
        pp_print_defn cx ff d
    | Fact (e, us, _) ->
        let ncx = Expr.Fmt.bump cx in
        fprintf ff "@[<h>%a@]" (pp_print_expr cx) e ;
        ncx

(** Extra function to print type annotation *)
and pp_print_optype ff = function
  | cx, Some t ->
      let env = Dq.fold_left
        (fun e h -> e $$ (h, hyp_optype h))
        empty (fst cx) in
      fprintf ff "::%a" ppt (env, t)
  | cx, None -> ()


(**
Refinements: In type [Ref(x, t, Ex(cx, ex))],
variable [x] is implicitly the
first element of [cx], that is,
[x] bounds the first De Bruijn index
(Ix 1) in [ex].
Functions: In type [Func(x, t1, t2)],
if [t2] matches [Ref(y, t, Ex(cx, ex))],
then [ex]'s context should be evaluated as
"cx @ [x]", where [y] is
already the first element of [cx].
*)
and ppt ppf (env, t) = match t with
    | Int ->
        fprintf ppf "Int"
    | Str ->
        fprintf ppf "Str"
    | Bool ->
        fprintf ppf "Bool"
    | TyAtom b ->
        fprintf ppf "#%s" b
    | Top ->
        fprintf ppf "T"
    | TyVar ([], x) ->
        fprintf ppf "\\%s" x
    | TyVar (ss, x) ->
        let ess = List.map
            (fun s -> env, s) ss in
        fprintf
            ppf
            "@[<h>(%s . @ @[<hv>[%a]@])@]"
            x (pp_print_delimited pp_ss) ess
    (*
    | EmptyVar x ->
        fprintf ppf "%s" x
    *)
    | Set t ->
        fprintf
            ppf
            "@[<h>(Set %a)@]"
            ppt (env, t)
    | Func ("", t1, t2) ->
        fprintf ppf
            "@[<hov>(%a ->@ %a)@]"
            ppt (env, t1) ppt (env, t2)
    | Func (x, t1, t2) ->
        fprintf
            ppf
            "@[<hov>((%s : %a) ->@ %a)@]"
            x ppt (env, t1) ppt
            (adj env (x, t1), t2)
    | Ref (_, Int, Ex (
            _,
            {core=Apply (
                {core=Internal B.Eq},
                [{core=Ix 1};
                 {core=Num (n, "")}])})) ->
        fprintf
            ppf
            "{%s}_Int" n
    | Ref (_, Int, Ex (
            _,
            {core=Apply (
                {core=Internal B.Lteq},
                [{core=Num ("0", "")};
                 {core=Ix 1}])})) ->
        fprintf
            ppf
            "[Nat]"
    | Ref (_, ((Int | Bool | Str) as b), Ex (
            _,
            {core=Internal B.TRUE})) ->
        fprintf
            ppf
            "[%a]"
            ppt (env, b)
    | Ref (x, ((Int | Str | Bool) as b), Ex (_, ex))
            when is_eq ex ->
        let ex = match ex.core with
            | Apply (
                    {core=Internal B.Eq},
                    [{core=Ix 1}; ex]) ->
                ex
            | _ ->
                assert false in
        fprintf
            ppf
            "{%a}_%a"
            (pp_print_expr (
                to_scx (adj env (x, b)),
                Ctx.dot))
            ex ppt (env, b)
    | Ref (x, ((Int | Str | Bool) as b), Ex (
            _,
            {core=List (Or, es)}))
                when for_all is_eq es ->
        let es = List.map
            (fun e ->
                match e.core with
                | Apply (
                        {core=Internal B.Eq},
                        [{core=Ix 1}; ex]) ->
                    ex
                | _ ->
                    assert false)
            es in
        fprintf
            ppf
            "{%a}_%a"
            (pp_print_delimited
                (pp_print_expr
                    (to_scx (adj env (x, b)),
                     Ctx.dot)))
            es ppt (env, b)
    | Ref (x, Int, Ex (
            _,
            {core=
                  (List (And, [
                    {core=Apply (
                        {core=Internal B.Lteq},
                        [a; {core=Ix 1}])};
                    {core=Apply (
                        {core=Internal B.Lteq},
                        [{core=Ix 1}; b])}]))
                | (Apply (
                    {core=Internal B.Conj}, [
                        {core=Apply (
                            {core=Internal B.Lteq},
                            [a; {core=Ix 1}])};
                        {core=Apply (
                            {core=Internal B.Lteq},
                            [{core=Ix 1}; b])}]))})) ->
        fprintf
            ppf
            "{%a .. %a}"
            (pp_print_expr
                (to_scx (adj env (x, Int)),
                 Ctx.dot))
            a
            (pp_print_expr
                (to_scx (adj env (x, Int)),
                 Ctx.dot))
            b
    | Ref (x, t, r) ->
        (* let r = add_x_ref x t r in *)
        fprintf
            ppf
            "@[<hov>{%s :@ %a |@ %a}@]"
            x ppt (env, t) pp_ref
            (adj env (x, t), r)
    (*
    | TySubst ([], t) ->
        fprintf
            ppf
            "@[<h>@[<hv>%a@]"
            ppt (env, t)
    | TySubst (ss, t) ->
        let ess = List.map
            (fun s -> env, s) ss in
        fprintf
            ppf
            "@[<h>(%a . @ @[<hv>[%a]@])@]"
            ppt (env, t)
            (pp_print_delimited pp_ss) ess
    *)
    (*
    | Emptyset ->
        pp_print_string
            ppf
            "00"  (* "{-}" *)
    *)
    (*
    | Emptyset t ->
        fprintf
            ppf
            "0(%a)"
            ppt t  (* "{-}" *)
    *)
    | Rec rs ->
        let ers = List.map
            (fun rs -> env, rs) rs in
        fprintf
            ppf
            "@[<hov>Rec{@[%a@]}@]"
            (pp_print_delimited pp_rec) ers
    | Rec_dot (t, h) ->
        fprintf
            ppf
            "@[<hov>(%a # %s)@]"
            ppt (env, t) h
    | TyPlus ts ->
        let pp_sep ff () = pp_print_string
            ff " ++ " in
        let ets = List.map
            (fun t -> env, t) ts in
        fprintf
            ppf
            "@[<hov>(%a)@]"
            (pp_print_delimited
                ~sep:pp_sep ppt)
            ets
    | TyTimes ts ->
        let pp_sep ff () = pp_print_string
            ff " xx " in
        let ets = List.map
            (fun t -> env, t) ts in
        fprintf
            ppf
            "@[<hov>(%a)@]"
            (pp_print_delimited
                    ~sep:pp_sep ppt)
            ets
    | Tbase t ->
        fprintf
            ppf
            "@[<h>(base %a)@]"
            ppt (env, t)
    | Tdom t ->
        fprintf
            ppf
            "@[<h>(dom %a)@]"
            ppt (env, t)
    | Tcod t ->
        fprintf
            ppf
            "@[<h>(cod %a)@]"
            ppt (env, t)
and pp_ref ppf = function
    | env, Ex (_, e) ->
        fprintf
            ppf
            "@[<hv>%a@]"
            (pp_print_expr (to_scx env, Ctx.dot)) e
    | env, Ph ([], p) ->
        fprintf
            ppf
            "@[<hv>%s@]"
            p
    | env, Ph (ss, p) ->
        let ess = List.map
            (fun s -> env, s) ss in
        fprintf
            ppf
            "@[<hv>[%a].@ %s@]"
            (pp_print_delimited pp_ss) ess p
and pp_ss ppf = function
    | env, (v, _, e, t) ->
        fprintf
            ppf
            "@[<h>%s:%a <- %a@]"
            v ppt (env, t)
            (pp_print_expr (to_scx env, Ctx.dot))
            e
        (*
        fprintf
            ppf
            "@[<h>%s |=> %a:%a@]"
            v (print_prop ()) e ppt t
        *)
        (*
        fprintf
            ppf
            "@[<h>%s |=> %a@]"
            v (print_prop ())
            (Smtcommons.opaque cx e)
        *)
        (*
        fprintf
            ppf
            "@[<h>%s |=> %a@]"
            v (print_prop ()) (e)
        *)
and pp_rec ppf = function
    | env, (h, t) ->
        fprintf
            ppf
            "@[<hov>%s |-> %a@]"
            h ppt (env, t)

and pp ppf env =
    let pp_print_elem ppf = function (x, t) ->
        fprintf
            ppf
            "@[<h>%s:%a@]"
            x ppt (env, t)
    in
    match Dq.front env with
    | None ->
        ()
    | Some ((h, None), env) ->
        pp ppf env
    | Some ((h, Some t), env)
            when Dq.null env ->
        fprintf
            ppf
            "@[%a@]"
            pp_print_elem (hyp_name h, t)
    | Some ((h, Some t), env) ->
        fprintf
            ppf
            "@[<v>%a,@,%a@] "
            pp_print_elem (hyp_name h, t) pp env

(*
(** PP environment (old E.pp) *)
and pp ppf env =
    let pp_print_elem ppf (x, t) = fprintf
        ppf
        "@[<h>%s:%a@]"
        x ppt (env, t) in
    match env with
    | [] -> ()
    | [xt] ->
        fprintf
            ppf
            "@[%a@]"
            pp_print_elem xt
    | xt :: env ->
        fprintf
            ppf
            "@[<v>%a,@,%a@] "
            pp_print_elem xt pp env
*)

(****************************************************************************)


(****************************************************************************)
(** Type assignments (cont.)                                                *)
(****************************************************************************)

let tyvar_assignment_subst a t =
    begin
    try
        let (cxe, bvar, _) = SMap.find
            a !tyvar_assignment in
        (*
        (if bvar then
            Util.eprintf
                "  @[<h2>\\%s := %a@]"
                a T.pp t else ());
        *)
        (** update type in the
        other assignments *)
        tyvar_assignment := SMap.mapi
            begin fun _ (cxe, bvar, ot) ->
                let ot = match ot with
                    | Some t' ->
                        Some (T.subst a t t')
                    | None ->
                        None
                    in
                    (cxe, bvar, ot)
            end
            !tyvar_assignment;
        tyvar_assignment := SMap.add
            a (cxe, bvar, Some t)
            !tyvar_assignment
    with _ ->
        tyvar_assignment := SMap.add
            a (None, false, Some t)
            !tyvar_assignment;
    (*
    Util.eprintf
        "___type %s not found in tyvar_assignment!!"
        a;
    *)
    end

let tyvar_assignment_pp v =
    SMap.iter
        (fun k (cxe, bvar, typ) ->
            let cx, e = Option.default
                ([], Internal B.TRUE %% []) cxe in
            if bvar
                then (
                    Smtcommons.ifprint v
                        "@[<h2>\\%s |-> %a  ~  %a@]"
                        k ppt
                        (empty,
                         Option.default
                            (TyVar ([], k)) typ)
                        (pp_print_expr
                            (Smtcommons.to_scx cx,
                             Ctx.dot))
                        e)
                else ())
        !tyvar_assignment

let tyvar_assignment_simp () =
    tyvar_assignment := SMap.mapi
        begin fun _ (cxe, bvar, ot) ->
            let ot = match ot with
            | Some t -> Some (T.simplify t)
            | None -> None
            in
            (cxe, bvar, ot)
        end
        !tyvar_assignment
