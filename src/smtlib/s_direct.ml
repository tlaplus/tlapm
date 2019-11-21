(*
 * smtlib/direct.ml -- untyped encoding
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Builtin
open Property
open Ext

open S_t
open S_symbs


(** Context of evaluation *)

type scx =
  { hx  : hyp Deque.dq
  ; cx  : int Ctx.t
  }


let bump scx = { scx with cx = Ctx.bump scx.cx }

let adj scx smb =
  let cx' = Ctx.push scx.cx smb in
  { scx with cx = cx' },
  Ctx.string_of_ident (Ctx.front cx')

let rec adjs scx smbs =
  match smbs with
  | [] -> scx, []
  | smb :: smbs ->
      let scx', x = adj scx smb in
      let scx', xs = adjs scx' smbs in
      scx', x :: xs


module Store = struct
  type key = int
  let to_int k = k

  module IntM = Map.Make (struct
    type t = key
    let compare = Pervasives.compare
  end)

  type elt = SmbSet.t * term
  let store = ref IntM.empty

  let mk_key e =
    let k = IntM.cardinal !store + 1 in
    store := IntM.add k e !store;
    k

  let get k = IntM.find k !store
end


(** Theory Management *)

type direct_req =
  | Core of core_smb_t
  | Ints of ints_smb_t
  | Sets of sets_smb_t
  | Bools of bools_smb_t
  | Strings of strings_smb_t
  | UInts of uints_smb_t
  | Funs of funs_smb_t
  | Tuples of tuples_smb_t
  | Recs of recs_smb_t

  | New of symbol * int

  | CompSet of symbol * Store.key
  | SubsSet of symbol list * Store.key
  | Fun of symbol list * Store.key
  | Epsilon of symbol * Store.key

module DDeps = struct
  type req = direct_req

  let get_symbol req =
    match req with
    | Core csmb     -> core_smb csmb
    | Ints ismb     -> ints_smb ismb
    | Sets ssmb     -> sets_smb ssmb
    | Bools bsmb    -> bools_smb bsmb
    | Strings ssmb  -> strings_smb ssmb
    | UInts ismb    -> uints_smb ismb
    | Tuples tsmb   -> tuples_smb tsmb
    | Funs fsmb     -> funs_smb fsmb
    | Recs rsmb     -> recs_smb rsmb

    | New (smb, _)  -> smb  (* No arity overloading assumed *)

    | CompSet (_, key)  -> "cmp_set_" ^ string_of_int (Store.to_int key)
    | SubsSet (_, key)  -> "subst_set_" ^ string_of_int (Store.to_int key)
    | Fun (_, key)      -> "fun_" ^ string_of_int (Store.to_int key)
    | Epsilon (_, key)  -> "eps_" ^ string_of_int (Store.to_int key)


  let get_decl req =
    match req with
    | Core csmb     -> core_decl csmb
    | Ints ismb     -> ints_decl ismb
    | Sets ssmb     -> sets_decl ssmb
    | Bools bsmb    -> bools_decl bsmb
    | Strings ssmb  -> strings_decl ssmb
    | UInts ismb    -> uints_decl ismb
    | Funs fsmb     -> funs_decl fsmb
    | Tuples tsmb   -> tuples_decl tsmb
    | Recs rsmb     -> recs_decl rsmb

    | New (smb, n)  ->
        let u_sort = sort (sets_smb U) in
        mk_op_decl smb (List.init n (fun _ -> u_sort), u_sort)

    | CompSet (_, key) ->
        let u_sort = sort (sets_smb U) in
        let smb = get_symbol req in

        let pars, _ = Store.get key in
        let n = SmbSet.cardinal pars in

        let rank = List.init (n+1) (fun _ -> u_sort) in
        let rank = rank, u_sort in
        mk_op_decl smb rank

    | Fun (xs, key) | SubsSet (xs, key) ->
        let u_sort = sort (sets_smb U) in
        let smb = get_symbol req in

        let pars, _ = Store.get key in
        let n = SmbSet.cardinal pars in
        let m = List.length xs in

        let rank = List.init (m+n) (fun _ -> u_sort) in
        let rank = rank, u_sort in
        mk_op_decl smb rank

    | Epsilon (_, key) ->
        let u_sort = sort (sets_smb U) in
        let smb = get_symbol req in

        let pars, _ = Store.get key in
        let n = SmbSet.cardinal pars in

        let rank = List.init n (fun _ -> u_sort) in
        let rank = rank, u_sort in
        mk_op_decl smb rank


  (* Ignore dependencies on core symbols; they are all declared *)
  let deps req =
    match req with
    (* Sets *)
    | Sets U    -> []
    | Sets In   -> [Sets U]
    | Sets _
    | CompSet _
    | SubsSet _ -> [Sets U; Sets In]
    (* Bools *)
    | Bools BSet          -> [Sets U; Sets In; Bools BCast]
    | Bools BCast         -> [Sets U]
    (* Strings *)
    | Strings (SLit _)    -> [Strings SSort]
    | Strings SSet        -> [Sets U; Sets In; Strings SSort; Strings SCast]
    | Strings SCast       -> [Sets U; Strings SSort]
    (* Ints *)
    | UInts ISet          -> [Sets U; Sets In; UInts ICast]
    | UInts NSet          -> [Sets U; Sets In; UInts ICast;
                              UInts ISet; UInts ILe]
    | UInts ICast         -> [Sets U]
    | UInts IRange        -> [Sets U; Sets In; UInts ILe]
    | UInts _             -> [Sets U; UInts ICast]
    (* Functions *)
    | Funs DomSet
    | Funs FunApp         -> [Sets U]
    | Funs _              -> [Sets U; Sets In; Funs DomSet; Funs FunApp]
    | Fun (xs, _)         ->
        let n = List.length xs in
        if n = 1 then
          [Sets U; Sets In; Funs DomSet; Funs FunApp]
        else
          [Sets U; Sets In; Funs DomSet; Funs FunApp;
           Tuples (ProdSet n); Tuples (Tuple n)]
    (* Tuples *)
    | Tuples ProdSet n    -> [Sets U; Sets In; Tuples (Tuple n)]
    | Tuples Tuple _      -> [Sets U; Funs DomSet; Funs FunApp;
                              UInts ICast; UInts IRange]
    (* Records *)
    | Recs (RecSet n)
    | Recs (Record n)     -> [Sets U; Sets In; Sets (SetEnum n);
                              Funs DomSet; Funs FunApp]
    (* Choose *)
    | Epsilon _           -> [Sets U]

    (* Others *)
    | New _     -> [Sets U]
    | _         -> []


  (* Strings or which a new symbol was declared.
   * Needed for the axiom scheme of unequality. *)
  let strings = ref []

  (* For each pair of cast functions, there is an axiom. *)
  type a_sorts = ABool | AInt | AString
  let a_declared = ref []

  let to_sort_and_cast = function
    | ABool   -> core_smb CoreBool, bools_smb BCast
    | AInt    -> ints_smb IntsInt,  uints_smb ICast
    | AString -> strings_smb SSort, strings_smb SCast

  let axioms req =
    let module A = S_axioms in

    match req with
    | Sets In             -> [(*A.set_ext*)] (* NOTE: Inefficient? *)
    | Sets Subset         -> [A.subset_def]
    | Sets SetEnum n      -> A.enum_set_car n
                             :: (if n = 0 then [A.empty_ext] else [])
    | Sets PowerSet       -> [A.power_set_car]
    | Sets UnionSet       -> [A.union_set_car]
    | Sets Inter          -> [A.inter_car]
    | Sets Union          -> [A.union_car]
    | Sets Diff           -> [A.diff_car]

    | Bools BSet          -> [A.bool_set_car]
    | Bools BCast         ->
        let sc = to_sort_and_cast ABool in
        let l = List.fold_left begin fun l a ->
          let ax = A.no_intersect (to_sort_and_cast a) sc in
          ax :: l
        end [] !a_declared in
        a_declared := ABool :: !a_declared;
        A.bool_cast_inj :: l

    | Strings SSet        -> [A.string_set_car]
    | Strings (SLit this_s) ->
        let l = !strings in
        strings := this_s :: !strings;
        let this_smb = strings_smb (SLit this_s) in
        List.map (fun other_s ->
          A.string_distinct this_smb (strings_smb (SLit other_s))) l
    | Strings SCast       ->
        let sc = to_sort_and_cast AString in
        let l = List.fold_left begin fun l a ->
          let ax = A.no_intersect (to_sort_and_cast a) sc in
          ax :: l
        end [] !a_declared in
        a_declared := AString :: !a_declared;
        A.string_cast_inj :: l

    | UInts ISet          -> [A.int_set_car]
    | UInts NSet          -> [A.nat_set_car]
    | UInts ICast         ->
        let sc = to_sort_and_cast AInt in
        let l = List.fold_left begin fun l a ->
          let ax = A.no_intersect (to_sort_and_cast a) sc in
          ax :: l
        end [] !a_declared in
        a_declared := AInt :: !a_declared;
        A.int_cast_inj :: l
    | UInts IPlus         -> [A.int_plus_hom]
    | UInts IMinus        -> [A.int_minus_hom]
    | UInts IMult         -> [A.int_mult_hom]
    | UInts IDiv          -> [A.int_div_hom]
    | UInts IMod          -> [A.int_mod_hom]
    | UInts ILe           -> [A.int_le_hom]
    | UInts IRange        -> [A.range_car]

    | Tuples (ProdSet n)  -> [A.prod_set_car n; A.tuple_ext n]
    | Tuples (Tuple n)    -> A.tuple_dom n :: List.init n (fun i -> A.tuple_def n (i+1))

    | Funs FunSet         -> [(*A.fun_ext (* NOTE: Inefficient? *)
                             ;*)A.fun_set_car]
    | Funs FunExcept      -> [A.fun_except_dom
                             ;A.fun_except_val]

    | Recs (RecSet n)     -> [A.rec_set_car n]
    | Recs (Record n)     -> [A.record_def n; A.record_dom n]

    | CompSet (x, key)    ->
        let and_smb = core_smb CoreAnd in
        let eq_smb  = core_smb CoreEq in
        let u_smb   = sets_smb U in
        let in_smb  = sets_smb In in
        let cmp_smb = get_symbol (CompSet (x, key)) in

        let pars, body = Store.get key in
        let pars = SmbSet.elements pars in
        let b = "base" in
        let args = b :: pars in

        let bd_u smb = (smb, sort u_smb) in
        [
          (* Comprehension set definition *)
          forall (List.map bd_u (List.append args [x])) (
            Annot (
              bin eq_smb (
                bin in_smb (cst x) (app cmp_smb (List.map cst args))
              ) (
                bin and_smb (bin in_smb (cst x) (cst b)) body
              ),
              ["pattern", Some (AttrList [
                bin in_smb (cst x) (app cmp_smb (List.map cst args))
              ])]
            )
          )
        ]

    | SubsSet (xs, key)   ->
        let and_smb = core_smb CoreAnd in
        let eq_smb  = core_smb CoreEq in
        let u_smb   = sets_smb U in
        let in_smb  = sets_smb In in
        let subs_set_smb  = get_symbol (SubsSet (xs, key)) in

        let n = List.length xs in
        let pars, body = Store.get key in
        let pars = SmbSet.elements pars in
        let bs = List.init n (fun i -> "base_" ^ string_of_int i) in
        let args = List.append bs pars in

        let bd_u x = (x, sort u_smb) in
        let y = "yy" in
        [
          (* Substitution set definition *)
          forall (List.map bd_u (List.append args [y])) (
            Annot (
              bin eq_smb (
                bin in_smb (cst y) (app subs_set_smb (List.map cst args))
              ) (
                exists (List.map bd_u xs) (
                  app and_smb (
                    bin eq_smb (cst y) body
                    :: List.map2 begin fun x b ->
                      bin in_smb (cst x) (cst b)
                    end xs bs
                  )
                )
              ),
              ["pattern", Some (AttrList [
                bin in_smb (cst y) (app subs_set_smb (List.map cst args))
              ])]
            )
          )
        ]

    | Fun (xs, key)       ->
        let eq_smb  = core_smb CoreEq in
        let imp_smb = core_smb CoreImp in
        let and_smb = core_smb CoreAnd in
        let u_smb   = sets_smb U in
        let in_smb  = sets_smb In in
        let dom_smb = get_symbol (Funs DomSet) in
        let app_smb = get_symbol (Funs FunApp) in
        let fcn_smb = get_symbol (Fun (xs, key)) in
        let tuple_smb n     = get_symbol (Tuples (Tuple n)) in
        let prod_set_smb n  = get_symbol (Tuples (ProdSet n)) in

        let pars, body = Store.get key in
        let pars = SmbSet.elements pars in
        let bs = List.init (List.length xs) (fun i -> "dom_" ^ string_of_int i) in
        let args = List.append bs pars in

        let bd_u x = (x, sort u_smb) in
        let n = List.length xs in
        [
          (* Explicit functions' definitions *)
          forall (List.map bd_u (List.append args xs)) (
            Annot (
              bin imp_smb (
                if n = 1 then
                  bin in_smb (cst (List.hd xs)) (cst (List.hd bs))
                else
                  app and_smb (List.map2 begin fun x b ->
                    bin in_smb (cst x) (cst b)
                  end xs bs)
              ) (
                bin eq_smb (
                  bin app_smb (
                    app fcn_smb (List.map cst args)
                  ) (
                    if n = 1 then cst (List.hd xs)
                    else
                      app (tuple_smb (n)) (List.map cst xs)
                  )
                )
                body
              ),
              ["pattern", Some (AttrList [
                bin app_smb (
                  app fcn_smb (List.map cst args)
                ) (
                  if n = 1 then cst (List.hd xs)
                  else
                    app (tuple_smb (n)) (List.map cst xs)
                )
              ])]
            )
          );
          (* Domain of explicit function *)
          forall (List.map bd_u args) (
            Annot (
              bin eq_smb (
                una dom_smb (app fcn_smb (List.map cst args))
              ) (
                if n = 1 then
                  cst (List.hd bs)
                else
                  app (prod_set_smb n) (List.map cst bs)
              ),
              ["pattern", Some (AttrList [
                una dom_smb (app fcn_smb (List.map cst args))
              ])]
            )
          )
        ]

    | Epsilon (x, key) ->
        let imp_smb = core_smb CoreImp in
        (*let eq_smb  = core_smb CoreEq in*)
        let u_smb   = sets_smb U in
        let eps_smb = get_symbol (Epsilon (x, key)) in

        let pars, body = Store.get key in
        let pars = SmbSet.elements pars in
        let args = pars in

        let bd_u smb = (smb, sort u_smb) in
        [
          (* Epsilon critical axiom *)
          forall (List.map bd_u (List.append args [x])) (
            Annot (
              bin imp_smb (body) (
                subst body x (app eps_smb (List.map cst args))
              ),
              ["pattern", Some (AttrList [ body ])]
            )
          )
          (* TODO: ext axioms *)
        ]

    | _ -> []
end

module DManager = TheoryManager (DDeps)
module M = DManager


type bsig = bool list * bool

let cast scx (actual : bool) (expected : bool) th t =
  match actual, expected with
  | true, true | false, false ->
      th, t
  | true, false ->
      let th', btou_dcl = M.ask th (Bools BCast) in
      th', una btou_dcl.smb t
  | false, true ->
      let th', eq_dcl = M.ask th (Core CoreEq) in
      let th', trueu_dcl = M.ask th' (Sets (SetEnum 0)) in
      th', bin eq_dcl.smb (cst trueu_dcl.smb) t

let rec enc_expr ?expect_bool:(bval=false) scx th e =
  let cast = cast scx in

  match e.core with
  | Ix _ | Opaque _ | Internal _ ->
      let th', smb, (_, bval') = enc_lexpr scx th e in
      cast bval' bval th' (cst smb)

  (* Ignore these *)
  | Apply ({ core = Internal Unprimable }, [e]) ->
      enc_expr ~expect_bool:bval scx th e

  | Apply (e, es) ->
      let th', smb, (bpars, bval') = enc_lexpr scx th e in

      (* A custom fold on two lists.
       * [bpars] is completed with [false]s if necessary, and additional
       * values in it are ignored. *)
      let th', es' =
        let rec aux (th, es') es bpars =
          match es, bpars with
          | [], _ ->
              (th, es')
          | e :: es,  [] ->
              let th', e' = enc_expr ~expect_bool:false scx th e in
              aux (th', e' :: es') es []
          | e :: es,  bval :: bpars ->
              let th', e' = enc_expr ~expect_bool:bval scx th e in
              aux (th', e' :: es') es bpars
        in
        aux (th', []) (List.rev es) (List.rev bpars)
      in

      cast bval' bval th' (app smb es')

  | If (e1, e2, e3) ->
      let th', e1' = enc_expr ~expect_bool:true scx th e1 in
      let th', e2' = enc_expr scx th' e2 in
      let th', e3' = enc_expr scx th' e3 in
      let th', ite_dcl = M.ask th' (Core CoreIte) in

      cast false bval th' (ter ite_dcl.smb e1' e2' e3')

  | List (Refs, []) ->
      let th', true_dcl = M.ask th (Core CoreTrue) in
      cast true bval th' (cst true_dcl.smb)
  | List (Refs, [e]) ->
      enc_expr ~expect_bool:bval scx th e

  | List (q, es) ->
      let th', op_dcl =
        match q with
        | And | Refs  -> M.ask th (Core CoreAnd)
        | Or          -> M.ask th (Core CoreOr)
      in

      let th', es' = List.fold_left begin fun (th, es') e ->
        let th', e' = enc_expr ~expect_bool:true scx th e in
        th', e' :: es'
      end (th', []) es in

      let e' = app op_dcl.smb es' in

      cast true bval th' e'

  | Let (dfs, e) ->
      let th', scx' = enc_defns scx th dfs in
      enc_expr ~expect_bool:bval scx' th' e

  | Quant (q, bs, e) ->
      (* The parsing of bounds records the optional domains [ds] of each variable
       * so those vars can be relativised in the result. *)
      let th', u_dcl = M.ask th (Sets U) in
      let top_scx = scx in

      let scx', th', bs', dom_hyps =
        let rec parse_bounds scx th bs (last_dom : term option) acc_bs acc_hs =
          match bs with
          | [] -> scx, th, acc_bs, acc_hs
          | (h, _, d) :: bs ->
              let scx', x = adj scx h.core in
              let b' = (x, sort u_dcl.smb) in
              let acc_bs' = b' :: acc_bs in

              match d, last_dom with
              | No_domain, _ | Ditto, None ->
                  parse_bounds scx' th bs None acc_bs' acc_hs

              | Domain e, _ ->
                  (* e is evaluated in the context above quantifiers *)
                  let th', e' = enc_expr top_scx th e in
                  let acc_hs' = (h.core, e') :: acc_hs in
                  parse_bounds scx' th' bs (Some e') acc_bs' acc_hs'

              | Ditto, Some e' ->
                  let acc_hs' = (h.core, e') :: acc_hs in
                  parse_bounds scx' th bs (Some e') acc_bs' acc_hs'
        in
        parse_bounds scx th' bs None [] []
      in

      let th', e' = enc_expr ~expect_bool:true scx' th' e in

      let th', e' =
        if List.length dom_hyps = 0 then
          th', e'
        else
          let th', in_dcl = M.ask th' (Sets In) in
          let th', op_dcl =
            match q with
            | Forall -> M.ask th' (Core CoreImp)
            | Exists -> M.ask th' (Core CoreAnd)
          in
          let hyps = List.map begin fun (x, t) ->
            bin in_dcl.smb (cst x) t
          end (List.rev dom_hyps) in
          th', app op_dcl.smb (List.append hyps [e'])
      in

      let q' = enc_quant q in
      cast true bval th' (Quant (q', List.rev bs', e'))

  | Tquant (q, hs, e) ->
      let th', u_dcl = M.ask th (Sets U) in

      let scx', xs = adjs scx (List.map (fun h -> h.core) hs) in
      let th', e' = enc_expr ~expect_bool:true scx' th' e in

      let bs' = List.map (fun x -> (x, sort u_dcl.smb)) xs in
      let q' = enc_quant q in
      cast true bval th' (Quant (q', List.rev bs', e'))

  | Choose (h, e1_opt, e2) ->
      let th', e1_opt' =
        match e1_opt with
        | None -> th, None
        | Some e1 ->
            let th', e1' = enc_expr scx th e1 in
            th', Some e1'
      in
      let scx', x = adj scx h.core in
      let th', e2' = enc_expr ~expect_bool:true scx' th' e2 in

      let cx =
        SmbSet.singleton x
        |> Deque.fold_right SmbSet.add th'.ops
      in
      let fvs = fv cx e2' in
      let fvs =
        match e1_opt' with
        | None -> fvs
        | Some e1' ->
            SmbSet.union fvs (fv cx e1')
      in

      let th', e' =
        match e1_opt' with
        | None -> th', e2'
        | Some e1' ->
            let th', and_dcl = M.ask th' (Core CoreAnd) in
            let th', in_dcl = M.ask th' (Sets In) in
            th', bin and_dcl.smb (bin in_dcl.smb (cst x) e1') e2'
      in
      let key = Store.mk_key (fvs, e') in
      let th', eps_dcl = M.ask th' (Epsilon (x, key)) in

      let pars = SmbSet.elements fvs in
      let pars = List.map cst pars in
      cast false bval th' (app eps_dcl.smb pars)

  | SetSt (h, e1, e2) ->
      let th', e1' = enc_expr scx th e1 in
      let scx', x = adj scx h.core in
      let th', e2' = enc_expr ~expect_bool:true scx' th' e2 in

      (* NOTE: which symbols should not be counted as parameters
       * is not very clear. *)
      let cx =
        SmbSet.singleton x
        |> Deque.fold_right SmbSet.add th'.ops
      in
      let fvs = fv cx e2' in

      let key = Store.mk_key (fvs, e2') in
      let th', cmp_dcl = M.ask th' (CompSet (x, key)) in

      let pars = SmbSet.elements fvs in
      let pars = List.map cst pars in
      cast false bval th' (app cmp_dcl.smb (e1' :: pars))

  | SetOf (e, bs) ->
      let top_scx = scx in

      let scx', th', vars, bounds =
        let rec parse_bounds scx th bs (last_dom : term option) acc_vars acc_hs =
          match bs with
          | [] -> scx, th, List.rev acc_vars, List.rev acc_hs
          | (h, _, d) :: bs ->
              let scx', x = adj scx h.core in
              let acc_vars = x :: acc_vars in

              match d, last_dom with
              | Domain e, _ ->
                  (* e is evaluated in the context above quantifiers! *)
                  let th', e' = enc_expr top_scx th e in
                  let acc_hs' = e' :: acc_hs in
                  parse_bounds scx' th' bs (Some e') acc_vars acc_hs'

              | Ditto, Some e' ->
                  let acc_hs' = e' :: acc_hs in
                  parse_bounds scx' th bs (Some e') acc_vars acc_hs'

              | No_domain, _ | Ditto, None ->
                  failwith "Smtlib.Direct.enc_expr: Missing bound in SetOf"
        in
        parse_bounds scx th bs None [] []
      in

      let th', e' = enc_expr scx' th' e in

      let cx =
        SmbSet.of_list vars
        |> Deque.fold_right SmbSet.add th'.ops
      in
      let fvs = fv cx e' in

      let key = Store.mk_key (fvs, e') in
      let th', subs_set_dcl = M.ask th' (SubsSet (vars, key)) in

      let pars = SmbSet.elements fvs in
      let pars = List.map cst pars in
      cast false bval th' (app subs_set_dcl.smb (List.append bounds pars))

  | SetEnum es ->
      let th', es' = List.fold_left begin fun (th, es') e ->
        let th', e' = enc_expr scx th e in
        th', e' :: es'
      end (th, []) (List.rev es) in
      let th', enum_dcl = M.ask th' (Sets (SetEnum (List.length es))) in

      cast false bval th' (app enum_dcl.smb es')

  | Product es ->
      let th', es' = List.fold_left begin fun (th, es') e ->
        let th', e' = enc_expr scx th e in
        th', e' :: es'
      end (th, []) (List.rev es) in
      let th', prod_set_dcl = M.ask th' (Tuples (ProdSet (List.length es))) in

      cast false bval th' (app prod_set_dcl.smb es')

  | Tuple es ->
      let th', es' = List.fold_left begin fun (th, es') e ->
        let th', e' = enc_expr scx th e in
        th', e' :: es'
      end (th, []) (List.rev es) in
      let th', tuple_dcl = M.ask th' (Tuples (Tuple (List.length es))) in

      cast false bval th' (app tuple_dcl.smb es')

  | Fcn (bs, e) ->
      let top_scx = scx in

      let scx', th', vars, bounds =
        let rec parse_bounds scx th bs (last_dom : term option) acc_vars acc_hs =
          match bs with
          | [] -> scx, th, List.rev acc_vars, List.rev acc_hs
          | (h, _, d) :: bs ->
              let scx', x = adj scx h.core in
              let acc_vars = x :: acc_vars in

              match d, last_dom with
              | Domain e, _ ->
                  (* e is evaluated in the context above quantifiers! *)
                  let th', e' = enc_expr top_scx th e in
                  let acc_hs' = e' :: acc_hs in
                  parse_bounds scx' th' bs (Some e') acc_vars acc_hs'

              | Ditto, Some e' ->
                  let acc_hs' = e' :: acc_hs in
                  parse_bounds scx' th bs (Some e') acc_vars acc_hs'

              | No_domain, _ | Ditto, None ->
                  failwith "Smtlib.Direct.enc_expr: Missing bound in Fcn"
        in
        parse_bounds scx th bs None [] []
      in

      let th', e' = enc_expr scx' th' e in

      let cx =
        SmbSet.of_list vars
        |> Deque.fold_right SmbSet.add th'.ops
      in
      let fvs = fv cx e' in

      let key = Store.mk_key (fvs, e') in
      let th', fcn_dcl = M.ask th' (Fun (vars, key)) in

      let pars = SmbSet.elements fvs in
      let pars = List.map cst pars in
      cast false bval th' (app fcn_dcl.smb (List.append bounds pars))

  | FcnApp (e, es) ->
      let th', e' = enc_expr scx th e in
      let th', es' =
        List.fold_left begin fun (th, es') e ->
          let th', e' = enc_expr scx th e in
          th', e' :: es'
        end (th', []) (List.rev es)
      in

      let th', app_dcl = M.ask th' (Funs FunApp) in

      begin match es' with
      | [] -> failwith "Smtlib.Direct.enc_expr: FcnApp with 0 arguments"
      | [e2'] ->
          cast false bval th' (bin app_dcl.smb e' e2')
      | es' ->
          let n = List.length es' in
          let th', tup_dcl = M.ask th' (Tuples (Tuple n)) in
          cast false bval th' (bin app_dcl.smb e' (app tup_dcl.smb es'))
      end

  | Arrow (e1, e2) ->
      let th', e1' = enc_expr scx th e1 in
      let th', e2' = enc_expr scx th' e2 in
      let th', arrow_dcl = M.ask th' (Funs FunSet) in

      cast false bval th' (bin arrow_dcl.smb e1' e2')

  | Rect fes ->
      let fs, es = List.split fes in
      let th', es' = List.fold_left begin fun (th, es') e ->
        let th', e' = enc_expr scx th e in
        th', e' :: es'
      end (th, []) es in

      let th', rec_set_dcl = M.ask th' (Recs (RecSet (List.length fes))) in
      let th', string_cast_dcl = M.ask th' (Strings SCast) in

      let th', fs' = List.fold_left begin fun (th, fs') str ->
        let th', fld_dcl = M.ask th (Strings (SLit str)) in
        th', una string_cast_dcl.smb (cst fld_dcl.smb) :: fs'
      end (th', []) fs in

      cast false bval th' (app rec_set_dcl.smb (List.append (List.rev fs') (List.rev es')))

  | Record fes ->
      let fs, es = List.split fes in
      let th', es' = List.fold_left begin fun (th, es') e ->
        let th', e' = enc_expr scx th e in
        th', e' :: es'
      end (th, []) es in

      let th', record_dcl = M.ask th' (Recs (Record (List.length fes))) in
      let th', string_cast_dcl = M.ask th' (Strings SCast) in

      let th', fs' = List.fold_left begin fun (th, fs') str ->
        let th', fld_dcl = M.ask th (Strings (SLit str)) in
        th', una string_cast_dcl.smb (cst fld_dcl.smb) :: fs'
      end (th', []) fs in

      cast false bval th' (app record_dcl.smb (List.append (List.rev fs') (List.rev es')))

  | Except (e1, [[Except_apply e2], e3]) ->
      let th', e1' = enc_expr scx th e1 in
      let th', e2' = enc_expr scx th' e2 in
      let th', e3' = enc_expr scx th' e3 in
      let th', except_dcl = M.ask th' (Funs FunExcept) in

      cast false bval th' (ter except_dcl.smb e1' e2' e3')

  | Except (e1, [[Except_dot str], e2]) ->
      let th', e1' = enc_expr scx th e1 in
      let th', e2' = enc_expr scx th' e2 in
      let th', except_dcl = M.ask th' (Funs FunExcept) in
      let th', fdl_dcl = M.ask th' (Strings (SLit str)) in
      let th', strtou_dcl = M.ask th' (Strings SCast) in

      cast false bval th' (ter except_dcl.smb e1' (una strtou_dcl.smb (cst fdl_dcl.smb)) e2')

  | Dot (e, str) ->
      let th', e' = enc_expr scx th e in
      let th', app_dcl = M.ask th' (Funs FunApp) in
      let th', fld_dcl = M.ask th' (Strings (SLit str)) in
      let th', strtou_dcl = M.ask th' (Strings SCast) in

      cast false bval th' (bin app_dcl.smb e' (una strtou_dcl.smb (cst fld_dcl.smb)))

  | String str ->
      let th', this_str_dcl = M.ask th (Strings (SLit str)) in
      let th', strtou_dcl = M.ask th' (Strings SCast) in
      cast false bval th' (una strtou_dcl.smb (cst this_str_dcl.smb))

  | Num (str, "") ->
      let th', i_to_u_dcl = M.ask th (UInts ICast) in
      let n = int_of_string str in
      cast false bval th' (una i_to_u_dcl.smb (intlit n))

  | _ -> Util.not_implemented "Smtlib.Direct.enc_expr"

and enc_quant = function
  | Forall -> Forall
  | Exists -> Exists

and enc_lexpr scx th e =
  match e.core with
  | Ix n ->
      let cx = scx.cx in
      let hx = scx.hx in
      let th', str = begin
        if n <= 0 then
          failwith "Smtlib.Direct.enc_expr: negative ix"
        else if n < Ctx.length cx then
          th, Ctx.string_of_ident (fst (Ctx.index cx n))
        else if n - Ctx.length cx < Deque.size hx then
          th, hyp_name (Option.get (Deque.nth ~backwards:true hx (n - Ctx.length cx - 1)))
        else
          failwith "Smtlib.Direct.enc_expr: too high ix"
      end in
      th', to_symbol str, ([], false)

  | Opaque s -> th, to_symbol s, ([], false)

  | Internal builtin ->
      let req, bpars, bval =
        match builtin with
        | TRUE      -> Core CoreTrue,   [],             true
        | FALSE     -> Core CoreFalse,  [],             true
        | Implies   -> Core CoreImp,    [true; true],   true
        | Equiv     -> Core CoreEq,     [true; true],   true
        | Conj      -> Core CoreAnd,    [true; true],   true
        | Disj      -> Core CoreOr,     [true; true],   true
        | Neg       -> Core CoreNot,    [true],         true
        | Eq        -> Core CoreEq,     [false; false], true
        | Neq       -> Core CoreNeq,    [false; false], true

        | STRING    -> Strings SSet,    [],             false
        | BOOLEAN   -> Bools BSet,      [],             false
        | SUBSET    -> Sets PowerSet,   [false],        false
        | UNION     -> Sets UnionSet,   [false],        false
        | DOMAIN    -> Funs DomSet,     [false],        false
        | Subseteq  -> Sets Subset,     [false; false], true
        | Mem       -> Sets In,         [false; false], true
        | Cap       -> Sets Inter,      [false; false], false
        | Cup       -> Sets Union,      [false; false], false
        | Setminus  -> Sets Diff,       [false; false], false

        | Int       -> UInts ISet,      [],             false
        | Nat       -> UInts NSet,      [],             false
        | Minus     -> UInts IMinus,    [false; false], false
        | Plus      -> UInts IPlus,     [false; false], false
        | Times     -> UInts IMult,     [false; false], false
        | Quotient  -> UInts IDiv,      [false; false], false
        | Remainder -> UInts IMod,      [false; false], false
        | Lteq      -> UInts ILe,       [false; false], true
        | Range     -> UInts IRange,    [false; false], false

        | Prime     -> New ("next_state", 1), [false],  false
        | _ -> Util.not_implemented "Smtlib.Direct.enc_lexpr"
      in
      let th', dcl = M.ask th req in
      th', dcl.smb, (bpars, bval)

  | _ -> Util.not_implemented "Smtlib.Direct.enc_lexpr"

and enc_sequent scx th sq =
  let th', scx' = enc_hyps scx th sq.context in
  let th', g = enc_expr ~expect_bool:true scx' th' sq.active in
  let th', h =
    let th', not_dcl = M.ask th' (Core CoreNot) in
    th', una not_dcl.smb g
  in
  let th' = add_assrt th' (mk_assrt ~name:"Goal" h) in
  th', scx'

and enc_hyps scx th hyps =
  (* NOTE: I don't see the queue of hypotheses being updated in Expr.Fmt.
   * Is this necessary? *)
  Deque.fold_left begin fun (th, scx) hyp ->
    let th', scx' = enc_hyp scx th hyp in
    let scx' = { scx' with hx = Deque.snoc scx'.hx hyp } in
    th', scx'
  end (th, scx) hyps

and enc_hyp scx th hyp =
  match hyp.core with
  | Fresh (h, Shape_op n, _, d) ->
      let th', _ = M.ask th (New (to_symbol h.core, n)) in
      let th' =
        match d with
        | Unbounded | Bounded (_, Hidden) -> th'
        | Bounded (e, Visible) ->
            (* Is this legal? *)
            failwith "Smtlib.Direct.enc_hyp"
      in
      let scx', _ = adj scx h.core in
      th', scx'

  | Fresh (h, Shape_expr, _, d) ->
      let th', _ = M.ask th (New (to_symbol h.core, 0)) in
      let th' =
        match d with
        | Unbounded | Bounded (_, Hidden) -> th'
        | Bounded (e, Visible) ->
            let th', e' = enc_expr scx th' e in
            let th', in_dcl = M.ask th' (Sets In) in
            let bound_hyp =
              bin in_dcl.smb (cst h.core) e'
            in
            let th' = add_assrt th' (mk_assrt bound_hyp) in
            th'
      in
      let scx', _ = adj scx h.core in
      th', scx'

  | Flex h ->
      let th', _ = M.ask th (New (to_symbol h.core, 0)) in
      let scx', _ = adj scx h.core in
      th', scx'

  | Fact (e, Visible, _) ->
      let th', t = enc_expr ~expect_bool:true scx th e in
      let th' = add_assrt th' (mk_assrt t) in
      let scx' = bump scx in
      th', scx'

  | Defn (defn, _, Visible, _) ->
      let th', scx' = enc_defn scx th defn in
      th', scx'

  | Fact (_, Hidden, _) ->
      th, bump scx
  | Defn (defn, _, Hidden, _) ->
      begin match defn.core with
      | Operator (h, { core = Lambda (xs, _) })
      | Bpragma  (h, { core = Lambda (xs, _) }, _) ->
          let th', _ = M.ask th (New (to_symbol h.core, List.length xs)) in
          let scx', _ = adj scx h.core in
          th', scx'
      | Operator (h, _) | Bpragma (h, _, _)
      | Recursive (h, _) | Instance (h, _) ->
          let th', _ = M.ask th (New (to_symbol h.core, 0)) in
          let scx', _ = adj scx h.core in
          th', scx'
      end

and enc_defns scx th dfs =
  List.fold_left begin fun (th, scx) df ->
    enc_defn scx th df
  end (th, scx) dfs

and enc_defn scx th df =
  match df.core with
  | Operator (h, { core = Lambda (xs, e) })
  | Bpragma  (h, { core = Lambda (xs, e) }, _) ->
      let th', dcl = M.ask th (New (to_symbol h.core, (List.length xs))) in
      let scx'', xs =
        let rec aux scx acc_xs = function
          | [] -> scx, acc_xs
          | (h, _) :: xs ->
              let scx', x = adj scx h.core in
              aux scx' (x :: acc_xs) xs
        in
        aux scx [] xs
      in
      let th', e' = enc_expr scx'' th e in

      let th', eq_dcl = M.ask th' (Core CoreEq) in
      let th', u_dcl = M.ask th' (Sets U) in
      let def_hyp =
          forall (List.map (fun x -> (x, sort u_dcl.smb)) xs) (
              bin eq_dcl.smb (cst dcl.smb) e'
          )
      in
      let assrt = mk_assrt ~name:("Definition '" ^ dcl.smb ^ "'") def_hyp in
      let th' = add_assrt th' assrt in

      let scx', _ = adj scx h.core in
      th', scx'

  | Operator (h, e)
  | Bpragma  (h, e, _) ->
      let th', dcl = M.ask th (New (to_symbol h.core, 0)) in
      let th', e' = enc_expr scx th e in

      let th', eq_dcl = M.ask th' (Core CoreEq) in
      let def_hyp =
          bin eq_dcl.smb (cst dcl.smb) e'
      in
      let assrt = mk_assrt ~name:("Definition '" ^ dcl.smb ^ "'") def_hyp in
      let th' = add_assrt th' assrt in

      let scx', _ = adj scx h.core in
      th', scx'

  | Recursive (h, _) ->
      let scx', _ = adj scx h.core in
      th, scx'
  | Instance (h, _) ->
      let scx', _ = adj scx h.core in
      th, scx'


(** We apply simple rewritings to make the translation easier.
    Erases the symbols: Notmem, Uminus, Lt, Gteq, Gt;
    Simplifies EXCEPT-expressions
*)
let normalize = object (self : 'self)
  inherit [unit] Expr.Visit.map as super

  method expr scx oe =
    match oe.core with
    | Apply ({ core = Internal Notmem } as e, es) ->
        Apply (Internal Neg %% [], [
          Apply (Internal Mem @@ e, es) @@ oe
        ]) %% [] |> self#expr scx
    | Apply ({ core = Internal Uminus } as e, es) ->
        Apply (Internal Minus @@ e, Num ("0", "") %% [] :: es)
        @@ oe |> self#expr scx

    | Apply ({ core = Internal Lt } as e, es) ->
        Apply (Internal Conj %% [], [
          Apply (Internal Lteq @@ e, es) @@ oe;
          Apply (Internal Neq %% [], es) %% []
        ]) %% [] |> self#expr scx
    | Apply ({ core = Internal Gteq } as e, es) ->
        Apply (Internal Disj %% [], [
          Apply (Internal Neg %% [], [
            Apply (Internal Lteq @@ e, es) @@ oe
          ]) %% [];
          Apply (Internal Eq %% [], es) %% []
        ]) %% [] |> self#expr scx
    | Apply ({ core = Internal Gt } as e, es) ->
        Apply (Internal Neg %% [], [
          Apply (Internal Lteq @@ e, es) @@ oe
        ]) %% [] |> self#expr scx

    | Except (e, ex1 :: ex2 :: exs) ->
        Except (
          Except (e, ex2 :: exs) %% [], [ex1]
        ) @@ oe |> self#expr scx
    | Except (e1, [Except_apply e2 :: exp :: exps, e3]) ->
        Except (
          e1, [[Except_apply e2],
            Except (FcnApp (e1, [e2]) %% [], [exp :: exps, e3]) %% []
          ]) @@ oe |> self#expr scx
    | Except (e1, [Except_dot str :: exp :: exps, e2]) ->
        Except (
          e1, [[Except_dot str],
            Except (Dot (e1, str) %% [], [exp :: exps, e2]) %% []
          ]) @@ oe |> self#expr scx

    | _ -> super#expr scx oe
end


let encode_direct sq =
  let scx =
    { hx = Deque.empty
    ; cx = Ctx.dot
    }
  in
  let th = ints_theory in
  let _, sq = normalize#sequent ((), Deque.empty) sq in
  enc_sequent scx th sq |> fst

