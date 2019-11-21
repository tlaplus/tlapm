(*
 * smtlib/symbs.ml -- manage symbols and declarations
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext

open S_t


(** Symbol Dependencies *)

module type S = sig
  type req
  type ans
  type s

  val solved  : s -> req -> bool
  val resolve : s -> req -> s
  val ask     : s -> req -> s * ans
end

module Sm = Util.Coll.Sm
module type Deps = sig
  type req  (** Unspecified *)

  val get_symbol  : req -> symbol
  val get_decl    : req -> decl

  val deps        : req -> req list
  val axioms      : req -> term list
end

module TheoryManager (D : Deps) = struct
  type req = D.req
  type ans = decl
  type s = theory

  (** TODO: Double-check this algorithm *)

  let solved th req =
    let smb = D.get_symbol req in
    mem th smb

  let rec resolve th req =
    if solved th req then th
    else begin
      let deps = D.deps req in
      let th' = List.fold_left resolve th deps in

      let axs = D.axioms req in
      let smb = D.get_symbol req in
      let assrts = List.mapi begin fun i ax ->
        mk_assrt ~name:("Axiom '" ^ smb ^ "' #" ^ string_of_int (i+1)) ax
      end axs in
      let th' = List.fold_left add_assrt th' assrts in

      let dcl = D.get_decl req in
      let th' = add_decl th' dcl in

      th'
    end

  let ask th req =
    let smb = D.get_symbol req in
    match find_opt th smb with
    | Some dcl ->
        th, dcl
    | None ->
        let th' = resolve th req in
        let dcl = find th' smb in
        th', dcl
end


(* Predefined Symbols *)

type core_smb_t =
  (* Sorts *)
  | CoreBool
  (* Operators *)
  | CoreTrue
  | CoreFalse
  | CoreNot
  | CoreImp
  | CoreAnd
  | CoreOr
  | CoreXor
  | CoreEq
  | CoreNeq
  | CoreIte

let core_smb = function
  | CoreBool  -> "Bool"
  | CoreTrue  -> "true"
  | CoreFalse -> "false"
  | CoreNot   -> "not"
  | CoreImp   -> "=>"
  | CoreAnd   -> "and"
  | CoreOr    -> "or"
  | CoreXor   -> "xor"
  | CoreEq    -> "="
  | CoreNeq   -> "distinct"
  | CoreIte   -> "ite"

let core_decl csmb =
  let smb = core_smb csmb in
  let bool_smb = core_smb CoreBool in
  match csmb with
  | CoreBool ->
      mk_sort_decl ~iscore:true smb 0
  | CoreTrue | CoreFalse ->
      mk_cst_decl ~iscore:true smb (sort bool_smb)
  | CoreNot ->
      mk_una_decl ~iscore:true smb (sort bool_smb) (sort bool_smb)
  | CoreImp | CoreAnd | CoreOr | CoreXor ->
      mk_bin_decl ~iscore:true smb (sort bool_smb) (sort bool_smb) (sort bool_smb)
  | CoreEq | CoreNeq ->
      let var = "a" in
      mk_bin_decl ~iscore:true smb ~pars:[var] (sort var) (sort var) (sort bool_smb)
  | CoreIte ->
      let var = "a" in
      mk_ter_decl ~iscore:true smb ~pars:[var] (sort bool_smb) (sort var) (sort var) (sort var)

let core_theory =
  List.fold_left add_decl empty_theory
  [ core_decl CoreBool
  ; core_decl CoreTrue
  ; core_decl CoreFalse
  ; core_decl CoreNot
  ; core_decl CoreImp
  ; core_decl CoreAnd
  ; core_decl CoreOr
  ; core_decl CoreXor
  ; core_decl CoreEq
  ; core_decl CoreNeq
  ; core_decl CoreIte
  ]


type ints_smb_t =
  (* Sorts *)
  | IntsInt
  (* Operators *)
  | IntsSubs
  | IntsPlus
  | IntsMult
  | IntsDiv
  | IntsMod
  | IntsAbs
  | IntsLe
  | IntsLt
  | IntsGe
  | IntsGt

let ints_smb = function
  | IntsInt   -> "Int"
  | IntsSubs  -> "-"
  | IntsPlus  -> "+"
  | IntsMult  -> "*"
  | IntsDiv   -> "div"
  | IntsMod   -> "mod"
  | IntsAbs   -> "abs"
  | IntsLe    -> "<="
  | IntsLt    -> "<"
  | IntsGe    -> ">="
  | IntsGt    -> ">"

let ints_decl ismb =
  let smb = ints_smb ismb in
  let int_smb = ints_smb IntsInt in
  let bool_smb = core_smb CoreBool in
  match ismb with
  | IntsInt ->
      mk_sort_decl ~iscore:true smb 0
  | IntsAbs ->
      mk_una_decl ~iscore:true smb (sort int_smb) (sort int_smb)
  | IntsSubs | IntsPlus | IntsMult | IntsDiv | IntsMod ->
      mk_bin_decl ~iscore:true smb (sort int_smb) (sort int_smb) (sort int_smb)
  | IntsLe | IntsLt | IntsGe | IntsGt ->
      mk_bin_decl ~iscore:true smb (sort int_smb) (sort int_smb) (sort bool_smb)


let ints_theory =
  List.fold_left add_decl core_theory
  [ ints_decl IntsInt
  ; ints_decl IntsSubs
  ; ints_decl IntsPlus
  ; ints_decl IntsMult
  ; ints_decl IntsDiv
  ; ints_decl IntsMod
  ; ints_decl IntsAbs
  ; ints_decl IntsLe
  ; ints_decl IntsLt
  ; ints_decl IntsGe
  ; ints_decl IntsGt
  ]


(* Symbols of Untyped Encoding *)

type sets_smb_t =
  (* Sorts *)
  | U
  (* Predicates *)
  | In
  | Subset
  (* Operators *)
  | SetEnum of int
  | PowerSet
  | UnionSet
  | Inter
  | Union
  | Diff

let sets_smb = function
  | U         -> "uu"
  | In        -> "mem_rel"
  | Subset    -> "subset_rel"
  | SetEnum n -> "set_enum_" ^ string_of_int n
  | PowerSet  -> "power_set"
  | UnionSet  -> "union_set"
  | Inter     -> "inter_op"
  | Union     -> "union_op"
  | Diff      -> "diff_op"

let sets_decl ssmb =
  let smb = sets_smb ssmb in
  let u_smb = sets_smb U in
  let bool_smb = core_smb CoreBool in
  match ssmb with
  | U ->
      mk_sort_decl smb 0
  | In | Subset ->
      mk_bin_decl smb (sort u_smb) (sort u_smb) (sort bool_smb)
  | PowerSet | UnionSet ->
      mk_una_decl smb (sort u_smb) (sort u_smb)
  | Inter | Union | Diff ->
      mk_bin_decl smb (sort u_smb) (sort u_smb) (sort u_smb)
  | SetEnum n ->
      let rank = List.init n (fun _ -> sort u_smb), (sort u_smb) in
      mk_op_decl smb rank


type bools_smb_t =
  | BSet
  | BCast

let bools_smb = function
  | BSet    -> "bool_set"
  | BCast   -> "b_to_u"

let bools_decl bsmb =
  let smb = bools_smb bsmb in
  let u_smb = sets_smb U in
  let bool_smb = core_smb CoreBool in
  match bsmb with
  | BSet ->
      mk_cst_decl smb (sort u_smb)
  | BCast ->
      mk_una_decl smb (sort bool_smb) (sort u_smb)


type strings_smb_t =
  | SSort
  | SSet
  | SLit of string
  | SCast

let strings_smb = function
  | SSort     -> "sort_str"
  | SSet      -> "string_set"
  | SLit str  -> "slit_" ^ to_symbol str
  | SCast     -> "s_to_u"

let strings_decl ssmb =
  let smb = strings_smb ssmb in
  let u_smb = sets_smb U in
  let str_smb = strings_smb SSort in
  match ssmb with
  | SSort ->
      mk_sort_decl smb 0
  | SSet ->
      mk_cst_decl smb (sort u_smb)
  | SLit _ ->
      mk_cst_decl smb (sort str_smb)
  | SCast ->
      mk_una_decl smb (sort str_smb) (sort u_smb)


type uints_smb_t =
  | ISet | NSet
  | ICast
  | IPlus | IMinus | IMult | IDiv | IMod
  | ILe
  | IRange

let uints_smb = function
  | ISet    -> "int_set"
  | NSet    -> "nat_set"
  | ICast   -> "i_to_u"
  | IPlus   -> "iop_plus"
  | IMinus  -> "iop_minus"
  | IMult   -> "iop_mult"
  | IDiv    -> "iop_div"
  | IMod    -> "iop_mod"
  | ILe     -> "iop_le"
  | IRange  -> "range"

let uints_decl ismb =
  let smb = uints_smb ismb in
  let u_smb = sets_smb U in
  let bool_smb = core_smb CoreBool in
  let int_smb = ints_smb IntsInt in
  match ismb with
  | ISet | NSet ->
      mk_cst_decl smb (sort u_smb)
  | ICast ->
      mk_una_decl smb (sort int_smb) (sort u_smb)
  | IPlus | IMinus | IMult | IDiv | IMod | IRange ->
      mk_bin_decl smb (sort u_smb) (sort u_smb) (sort u_smb)
  | ILe ->
      mk_bin_decl smb (sort u_smb) (sort u_smb) (sort bool_smb)


type funs_smb_t =
  | FunSet
  | DomSet
  | FunApp
  | FunExcept

let funs_smb = function
  | FunSet    -> "arrow_set"
  | DomSet    -> "domain"
  | FunApp    -> "app"
  | FunExcept -> "except"

let funs_decl fsmb =
  let smb = funs_smb fsmb in
  let u_smb = sets_smb U in
  match fsmb with
  | FunSet | FunApp ->
      mk_bin_decl smb (sort u_smb) (sort u_smb) (sort u_smb)
  | DomSet ->
      mk_una_decl smb (sort u_smb) (sort u_smb)
  | FunExcept ->
      mk_ter_decl smb (sort u_smb) (sort u_smb) (sort u_smb) (sort u_smb)


type tuples_smb_t =
  | ProdSet of int
  | Tuple of int

let tuples_smb = function
  | ProdSet n -> "product_set_" ^ string_of_int n
  | Tuple n   -> "tuple_" ^ string_of_int n

let tuples_decl tsmb =
  let smb = tuples_smb tsmb in
  let u_smb = sets_smb U in
  match tsmb with
  | ProdSet n | Tuple n ->
      let rank = List.init n (fun _ -> sort u_smb), (sort u_smb) in
      mk_op_decl smb rank


type recs_smb_t =
  | RecSet of int
  | Record of int

let recs_smb = function
  | RecSet n  -> "record_set_" ^ string_of_int n
  | Record n  -> "record_" ^ string_of_int n

let recs_decl rsmb =
  let smb = recs_smb rsmb in
  let u_smb = sets_smb U in
  match rsmb with
  | RecSet n | Record n ->
      let rank = (List.init (2 * n) (fun _ -> sort u_smb)), (sort u_smb) in
      mk_op_decl smb rank

