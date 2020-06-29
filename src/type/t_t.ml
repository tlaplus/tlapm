(*
 * type/t.ml --- type system
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Util
open Format
open Fmtutil
open Property


(* {3 Generalities} *)

type ty =
  | TUnknown
  | TVar of string
  | TAtom of ty_atom
  | TSet of ty
  | TArrow of ty * ty
  | TProd of ty list
and ty_atom =
  | TU | TBool | TInt | TReal | TStr
and ty_kind =
  | TKind of ty_kind list * ty

module Sm = Coll.Sm
type tmap = ty Sm.t

let rec ord (TKind (ks, _)) =
  match ks with
  | [] -> 0
  | _ -> List.fold_left (fun m k -> max m (ord k)) 1 ks

let mk_atom_ty a = TAtom a

let mk_kind_ty ks ty  = TKind (ks, ty)
let mk_cstk_ty ty     = TKind ([], ty)
let mk_fstk_ty tys ty = TKind (List.map mk_cstk_ty tys, ty)

let get_atom = function
  | TAtom a -> a
  | _ -> invalid_arg "Type.T.get_atom: not an atomic type"

let get_ty = function
  | TKind ([], ty) -> ty
  | _ -> invalid_arg "Type.T.get_ty: not a constant operator type"

let ty_u = mk_atom_ty TU
let ty_bool = mk_atom_ty TBool
let ty_int = mk_atom_ty TInt
let ty_real = mk_atom_ty TReal
let ty_str = mk_atom_ty TStr

let rec get_types (TKind (ks, ty)) =
  let tss = List.map get_types ks in
  ty :: List.concat tss

let rec ty_to_string ty =
  match ty with
  | TUnknown -> "Unknown"
  | TVar a -> "Var" ^ a
  | TAtom a -> "Atom" ^ tyatom_to_string a
  | TSet ty -> "Set" ^ ty_to_string ty
  | TArrow (ty1, ty2) -> "Fun" ^ ty_to_string ty1 ^ ty_to_string ty2
  | TProd tys -> "Prod" ^ String.concat "" (List.map ty_to_string tys)
and tyatom_to_string a =
  match a with
  | TU -> "U"
  | TBool -> "Bool"
  | TInt -> "Int"
  | TReal -> "Real"
  | TStr -> "String"


(* {3 Type Annotations} *)

module Props = struct
  let type_prop = make "Type.T.Props.type_prop"
  let atom_prop = make "Type.T.Props.atom_prop"
  let kind_prop = make "Type.T.Props.kind_prop"
end

let annot_type h t = assign h Props.type_prop t
let annot_sort h s = assign h Props.atom_prop s
let annot_kind h k = assign h Props.kind_prop k

let has_type h = has h Props.type_prop
let has_sort h = has h Props.atom_prop
let has_kind h = has h Props.kind_prop

let get_type h = get h Props.type_prop
let get_sort h = get h Props.atom_prop
let get_kind h = get h Props.kind_prop

let query_type h = query h Props.type_prop
let query_sort h = query h Props.atom_prop
let query_kind h = query h Props.kind_prop


(* {3 Pretty-printing} *)

let rec pp_print_type ff ty =
  pp_print_tyarrow ff ty

and pp_print_tyarrow ff ty =
  match ty with
  | TArrow (ty1, ty2) ->
      fprintf ff "@[%a ->@ %a@]"
      pp_print_typrod ty1
      pp_print_tyarrow ty2
  | _ -> pp_print_typrod ff ty

and pp_print_typrod ff ty =
  match ty with
  | TProd tys ->
      pp_print_delimited ~sep:begin fun ff () ->
        pp_print_string ff " *";
        pp_print_space ff () end
      pp_print_tyset ff tys
  | _ -> pp_print_tyset ff ty

and pp_print_tyset ff ty =
  match ty with
  | TSet ty ->
      fprintf ff "@[%a set@]"
      pp_print_tyset ty
  | _ -> pp_print_tyatom ff ty

and pp_print_tyatom ff ty =
  match ty with
  | TVar x -> pp_print_string ff x
  | TAtom a -> pp_print_atom ff a
  | TUnknown -> pp_print_string ff "?"
  | _ -> fprintf ff "@[(%a@])" pp_print_tyarrow ty

and pp_print_atom ff a =
  match a with
  | TBool -> pp_print_string ff "bool"
  | TU -> pp_print_string ff "U"
  | TInt -> pp_print_string ff "int"
  | TReal -> pp_print_string ff "real"
  | TStr -> pp_print_string ff "string"

let rec pp_print_kind ff (TKind (ks, ty)) =
  fprintf ff "@[[%a@]]%a"
  (pp_print_delimited pp_print_kind) ks
  pp_print_type ty

