(*
 * smtlib/t.ml -- S-expressions
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext

exception Double_declaration


type symbol = string

let replacements =
  [ "\\\\", "_backslash_"
  ; "(",    "_lparen_"
  ; ")",    "_rparen_"
  ; "+",    "_plus_"
  ; "-",    "_minus_"
  ; "*",    "_star_"
  ; "/",    "_slash_"
  ; "%",    "_percent_"
  ; "<",    "_langle_"
  ; ">",    "_rangle_"
  ; "=",    "_equalsign_"
  ; "\\^",  "_circumflex_"
  ; "&",    "_ampersand_"
  ; "|",    "_bar_"
  ; "~",    "_tilde_"
  ; "!",    "_exclamation_"
  ; "?",    "_interrogation_"
  ; "\\.",  "_dot_"
  ; ":",    "_colon_"
  ; "#",    "_hash_"
  ; "@",    "_at_"
  ; "\\$",  "_dollarsign_"
  ; " ",    "_space_"
  ]

let to_symbol str =
  List.fold_left begin fun str (from_s, to_s) ->
    Str.global_replace (Str.regexp from_s) to_s str
  end str replacements

(** Terms and Formulas of SMT-LIB *)

type term =
  | Literal of lit
  | App of qual_ident * term list
  | Let of var_bind list * term
  | Quant of quant * sorted_bind list * term
  | Match of term * match_case list
  | Annot of term * attribute list

and lit =
  | LInt of int
  | LStr of string

and quant = Forall | Exists

and qual_ident =
  | Id of symbol
  | As of symbol * sort

and var_bind = symbol * term

and sorted_bind = symbol * sort

and match_case = pattern * term

and sort =
  | Sort of symbol * sort list

and pattern = symbol * symbol list

and attribute = symbol * attribute_val option
and attribute_val =
  | AttrLit of lit
  | AttrIdent of symbol
  | AttrList of term list


(** Constructor Utilities *)

let sort ?(pars=[]) smb = Sort (smb, pars)

let intlit n = Literal (LInt n)
let strlit s = Literal (LStr s)

let app smb ts = App (Id smb, ts)
let cst smb = app smb []
let una smb t1 = app smb [t1]
let bin smb t1 t2 = app smb [t1; t2]
let ter smb t1 t2 t3 = app smb [t1; t2; t3]

let forall sbs t = Quant (Forall, sbs, t)
let exists sbs t = Quant (Exists, sbs, t)
let lets vbs t = Let (vbs, t)
let cases t pcases = Match (t, pcases)

let pattern t pats =
    let attrv = ("pattern", Some (AttrList pats)) in
    match t with
    | Annot (t', attrs) -> Annot (t', attrv :: attrs)
    | _ -> Annot (t, [attrv])


(** Compare and Remember terms *)

module SmbSet = Set.Make (struct
  type t = symbol
  let compare = Pervasives.compare
end)

let fv ctx t =
  let rec fv_aux ctx t acc =
    match t with
    | Literal _ | Annot _ -> acc
    | App (Id smb, [])
    | App (As (smb, _), []) ->
        if SmbSet.mem smb ctx then acc
        else
          SmbSet.add smb acc
    | App (_, ts) ->
        List.fold_left begin fun acc t ->
          fv_aux ctx t acc
        end acc ts
    | Let (vbs, t) ->
        let acc', ctx' =
          List.fold_left begin fun (acc, ctx) (smb, t) ->
            let acc' = fv_aux ctx t acc in
            let ctx' = SmbSet.add smb ctx in
            (acc', ctx')
          end (acc, ctx) vbs
        in
        fv_aux ctx' t acc'
    | Quant (_, sbs, t) ->
        let sbs = List.map fst sbs in
        let ctx' = List.fold_right SmbSet.add sbs ctx in
        fv_aux ctx' t acc
    | Match (t, cs) ->
        let acc' = fv_aux ctx t acc in
        List.fold_left begin fun acc ((smb, smbs), t) ->
          let ctx' = List.fold_right SmbSet.add (smb :: smbs) ctx in
          fv_aux ctx' t acc
        end acc' cs
  in
  fv_aux ctx t SmbSet.empty

let rec subst t x v =
  match t with
  | App (Id smb, []) | App (As (smb, _), []) ->
      if smb = x then v
      else t
  | App (qual_id, ts) ->
      let ts' =
        List.fold_left begin fun ts t ->
          subst t x v :: ts
        end [] (List.rev ts)
      in
      App (qual_id, ts')
  | Let (vbs, t) ->
      let vbs', b =
        List.fold_left begin fun (vbs, b) (smb, t as vb) ->
          if not b then vb :: vbs, b
          else if smb = x then
            let t' = subst t x v in
            (smb, t') :: vbs, false
          else
            let t' = subst t x v in
            (smb, t') :: vbs, b
        end ([], true) vbs
      in
      let vbs' = List.rev vbs' in
      if not b then Let (vbs', t)
      else
        let t' = subst t x v in
        Let (vbs', t')
  | Quant (q, sbs, tt) ->
      if List.exists (fun (smb, _) -> smb = x) sbs then t
      else
        let tt' = subst tt x v in
        Quant (q, sbs, tt')
  | Match (t, cs) ->
      let t' = subst t x v in
      let cs' =
        List.fold_left begin fun cs ((smb, smbs as pat), t) ->
          if List.mem x (smb :: smbs) then (pat, t) :: cs
          else
            let t' = subst t x v in
            (pat, t') :: cs
        end [] (List.rev cs)
      in
      Match (t', cs')
  | Annot (t, l) ->
      let t' = subst t x v in
      let l' =
        List.map begin fun (smb, at_val) ->
          match at_val with
          | Some (AttrList ts) ->
              let ts' = List.map (fun t -> subst t x v) ts in
              (smb, Some (AttrList ts'))
          | _ -> (smb, at_val)
        end l
      in
      Annot (t', l')
  | _ -> t


(** Declarations and Theories *)

type kind = SortDecl | OpDecl

type decl =
  { kind : kind
  ; smb : symbol
  ; pars : symbol list
  ; rank : sort list * sort
  ; iscore : bool
  }

type assrt =
  { name : string
  ; form : term
  }

module Sm = Util.Coll.Sm
type theory =
  { decls   : decl Sm.t
  ; sorts   : symbol Deque.dq
  ; ops     : symbol Deque.dq
  ; assrts  : assrt Sm.t
  }


let dummy_sort = Sort ("", [])

let mk_sort_decl ?(iscore=false) smb n =
  { kind = SortDecl
  ; smb = smb
  ; pars = []
  ; rank = List.init n (fun _ -> dummy_sort), dummy_sort
  ; iscore = iscore
  }

let mk_op_decl ?(iscore=false) smb ?(pars=[]) rk =
  { kind = OpDecl
  ; smb = smb
  ; pars = pars
  ; rank = rk
  ; iscore = iscore
  }

let mk_cst_decl ?(iscore=false) smb ?(pars=[]) s1 =
  mk_op_decl ~iscore:iscore smb ~pars:pars ([], s1)

let mk_una_decl ?(iscore=false) smb ?(pars=[]) s1 s2 =
  mk_op_decl ~iscore:iscore smb ~pars:pars ([s1], s2)

let mk_bin_decl ?(iscore=false) smb ?(pars=[]) s1 s2 s3 =
  mk_op_decl ~iscore:iscore smb ~pars:pars ([s1; s2], s3)

let mk_ter_decl ?(iscore=false) smb ?(pars=[]) s1 s2 s3 s4 =
  mk_op_decl ~iscore:iscore smb ~pars:pars ([s1; s2; s3], s4)

let mk_assrt ?(name="") t =
  { name = name
  ; form = t
  }

let empty_theory =
  { decls = Sm.empty
  ; sorts = Deque.empty
  ; ops = Deque.empty
  ; assrts = Sm.empty
  }

let combine th1 th2 =
  Util.not_implemented ""


let mem th smb = Sm.mem smb th.decls
let find th smb = Sm.find smb th.decls

let find_opt th smb =
  try Some (Sm.find smb th.decls)
  with Not_found -> None

let update smb f sm =
  let y =
    try Some (Sm.find smb sm)
    with Not_found -> None
  in
  match f y with
  | None -> Sm.remove smb sm
  | Some x -> Sm.add smb x sm

let update_fcn a = function
  | None -> Some a
  | Some _ -> raise Double_declaration

let add_decl th dcl =
  match dcl.kind with
  | SortDecl ->
      { th with
        decls = update dcl.smb (update_fcn dcl) th.decls
      ; sorts = Deque.snoc th.sorts dcl.smb
      }
  | OpDecl ->
      { th with
        decls = update dcl.smb (update_fcn dcl) th.decls
      ; ops   = Deque.snoc th.ops dcl.smb
      }

let maybe_decl th dcl =
  try add_decl th dcl
  with Double_declaration -> th

let add_assrt th assrt =
  let key =
    match assrt.name with
    | "" ->
        let sz = Sm.cardinal th.assrts in
        let name = "__unnamed__assrt__sz" ^ (string_of_int sz) in
        name
    | _ -> assrt.name
  in
  { th with assrts = update key (update_fcn assrt) th.assrts }

