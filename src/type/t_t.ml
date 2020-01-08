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
  | TVar of string
  | TAtom of ty_atom
  | TArrow of ty * ty
  | TProd of ty list
  | TSet of ty
  | TUnknown
and ty_atom =
  | TBool | TAtSet | TInt | TReal | TStr

module Sm = Coll.Sm
type tmap = ty Sm.t

module Props = struct
  let type_prop = make "Type.T.Props.type_prop"
end

let ty_bool = TAtom TBool
let ty_aset = TAtom TAtSet
let ty_int = TAtom TInt
let ty_real = TAtom TReal
let ty_str = TAtom TStr

let get_atom = function
  | TAtom a -> a
  | _ -> invalid_arg "Type.T.get_atom: not an atomic type"

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
  | TAtSet -> pp_print_string ff "set"
  | TInt -> pp_print_string ff "int"
  | TReal -> pp_print_string ff "real"
  | TStr -> pp_print_string ff "string"


