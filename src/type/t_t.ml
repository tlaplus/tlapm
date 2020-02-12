(*
 * type/t.ml --- type system
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Format

open Util
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
and ty_op =
  | TOp of ty_op list * ty

module Sm = Coll.Sm
type tmap = ty Sm.t

module Props = struct
  let tyop_prop = make "Type.T.Props.tyop_prop"
  let type_prop = make "Type.T.Props.type_prop"
  let sort_prop = make "Type.T.Props.sort_prop"
end

let mk_atom_ty a = TAtom a

let mk_op_ty tyops ty  = TOp (tyops, ty)
let mk_cst_ty ty       = TOp ([], ty)
let mk_fstop_ty tys ty = TOp (List.map mk_cst_ty tys, ty)

let get_atom = function
  | TAtom a -> a
  | _ -> invalid_arg "Type.T.get_atom: not an atomic type"

let get_ty = function
  | TOp ([], ty) -> ty
  | _ -> invalid_arg "Type.T.get_ty: not a constant operator type"

let get_atoms ty =
  let add x l =
    if List.exists ((=) x) l then l else x :: l
  in
  let rec f acc = function
    | TAtom a -> add a acc
    | TSet ty -> f acc ty
    | TArrow (ty1, ty2) ->
        let acc = f acc ty1 in
        f acc ty2
    | TProd tys ->
        List.fold_left f acc tys
    | _ -> acc
  in
  f [] ty

let ty_u = mk_atom_ty TU
let ty_bool = mk_atom_ty TBool
let ty_int = mk_atom_ty TInt
let ty_real = mk_atom_ty TReal
let ty_str = mk_atom_ty TStr


(* {3 Type Annotations} *)

let type_annot h ty = assign h Props.type_prop ty

let has_type_annot h = has h Props.type_prop

let get_type_annot h = get h Props.type_prop

let get_opt_type_annot h = query h Props.type_prop


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
  | TAtom a -> pp_print_tatom ff a
  | TUnknown -> pp_print_string ff "?"
  | _ -> fprintf ff "@[(%a@])" pp_print_tyarrow ty

and pp_print_tatom ff a =
  match a with
  | TBool -> pp_print_string ff "bool"
  | TU -> pp_print_string ff "set"
  | TInt -> pp_print_string ff "int"
  | TReal -> pp_print_string ff "real"
  | TStr -> pp_print_string ff "string"


