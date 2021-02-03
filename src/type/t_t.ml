(*
 * type/t.ml --- type system
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Property
open Format


(* {3 Generalities} *)

type ty =
  | TVar of string  (** Type variable *)
  | TAtm of atm     (** Atomic type *)
  | TSet of ty      (** Set-type *)
  | TFun of ty * ty (** Function-type *)
  | TPrd of ty list (** Product-type *)
and atm =
  | TAIdv           (** Individual *)
  | TABol           (** Boolean *)
  | TAInt           (** Integer *)
  | TARel           (** Real *)
  | TAStr           (** String *)

and ty0 = ty
and ty1 = Ty1 of ty0 list * ty  (** Fst-order operator type *)
and ty2 = Ty2 of ty1 list * ty  (** Snd-order operator type *)

module Ts = Set.Make (struct
  type t = ty
  let compare = Pervasives.compare
end)

module Tm = Map.Make (struct
  type t = ty
  let compare = Pervasives.compare
end)

let upcast_ty1 ty = Ty1 ([], ty)
let upcast_ty2 (Ty1 (ty0s, ty)) = Ty2 (List.map upcast_ty1 ty0s, ty)

exception Invalid_type_downcast

let downcast_ty0 = function
  | Ty1 ([], ty) -> ty
  | _ -> raise Invalid_type_downcast

let downcast_ty1 (Ty2 (ty1s, ty)) = Ty1 (List.map downcast_ty0 ty1s, ty)

let safe_downcast_ty0 ty1 =
  try Some (downcast_ty0 ty1)
  with Invalid_type_downcast -> None

let safe_downcast_ty1 ty2 =
  try Some (downcast_ty1 ty2)
  with Invalid_type_downcast -> None


(* {3 Type Substitutions} *)

module Sm = Util.Coll.Sm

type ty_sub = ty Sm.t

let rec apply_ty_sub m ty =
  match ty with
  | TVar a when Sm.mem a m ->
      Sm.find a m
  | TSet ty ->
      TSet (apply_ty_sub m ty)
  | TFun (ty1, ty2) ->
      TFun (apply_ty_sub m ty1, apply_ty_sub m ty2)
  | TPrd tys ->
      TPrd (List.map (apply_ty_sub m) tys)
  | _ -> ty

let apply_ty_sub1 m ty1 =
  match ty1 with
  | Ty1 (ty0s, ty) ->
      Ty1 (List.map (apply_ty_sub m) ty0s, apply_ty_sub m ty)

let apply_ty_sub2 m ty2 =
  match ty2 with
  | Ty2 (ty1s, ty) ->
      Ty2 (List.map (apply_ty_sub1 m) ty1s, apply_ty_sub m ty)


(* {3 Type Erasure} *)

let erase0 ty0 =
  match ty0 with
  | TAtm TABol -> TAtm TABol
  | _ -> TAtm TAIdv

let erase1 (Ty1 (ty0s, ty)) =
  Ty1 (List.map erase0 ty0s, erase0 ty)

let erase2 (Ty2 (ty1s, ty)) =
  Ty2 (List.map erase1 ty1s, erase0 ty)


(* {3 Type Annotations} *)

module Props = struct
  let ty0_prop = make "Type.T.Props.ty0_prop"
  let ty1_prop = make "Type.T.Props.ty1_prop"
  let ty2_prop = make "Type.T.Props.ty2_prop"

  let tpars_prop = make "Type.T.Props.tpars_prop"
  let icast_prop = make "Type.T.Props.icast_prop"
  let bproj_prop = make "Type.T.Props.bproj_prop"
end


(* {3 Pretty-printing} *)

let rec ty_to_string ty =
  match ty with
  | TVar a -> "Var" ^ a
  | TAtm a -> tyatom_to_string a
  | TSet ty -> "Set" ^ ty_to_string ty
  | TFun (ty1, ty2) -> "Fun" ^ ty_to_string ty1 ^ ty_to_string ty2
  | TPrd tys -> List.fold_left (fun s ty -> s ^ ty_to_string ty) "Prd" tys
and tyatom_to_string a =
  match a with
  | TAIdv -> "Idv"
  | TABol -> "Bool"
  | TAInt -> "Int"
  | TARel -> "Real"
  | TAStr -> "String"


let rec pp_print_ty0 ff ty =
  pp_print_tyarrow ff ty

and pp_print_tyarrow ff ty =
  match ty with
  | TFun (ty1, ty2) ->
      fprintf ff "@[fun(%a,@ %a@])"
      pp_print_tyset ty1
      pp_print_tyarrow ty2
  | _ -> pp_print_typrod ff ty

and pp_print_typrod ff ty =
  match ty with
  | TPrd tys ->
      fprintf ff "@[prod(%a@])"
      (Fmtutil.pp_print_delimited pp_print_tyset) tys
  | _ -> pp_print_tyset ff ty

and pp_print_tyset ff ty =
  match ty with
  | TSet ty ->
      fprintf ff "@[set(%a@])"
      pp_print_tyset ty
  | _ -> pp_print_tyatom ff ty

and pp_print_tyatom ff ty =
  match ty with
  | TVar x -> pp_print_string ff x
  | TAtm a -> pp_print_atm ff a
  | _ -> fprintf ff "@[(%a@])" pp_print_ty0 ty

and pp_print_atm ff a =
  match a with
  | TAIdv -> pp_print_string ff "iota"
  | TABol -> pp_print_string ff "bool"
  | TAInt -> pp_print_string ff "int"
  | TARel -> pp_print_string ff "real"
  | TAStr -> pp_print_string ff "string"


let pp_print_times ff () =
  fprintf ff "@ * "

let pp_print_ty1 ff ty1 =
  match ty1 with
  | Ty1 (ty0s, ty) ->
      fprintf ff "%a@ -> %a"
      (Fmtutil.pp_print_delimited ~sep:pp_print_times pp_print_ty0) ty0s
      pp_print_ty0 ty

let pp_print_ty1_parens ff ty1 =
  match ty1 with
  | Ty1 ([], ty) -> pp_print_ty0 ff ty
  | _ -> Fmtutil.pp_print_with_parens pp_print_ty1 ff ty1

let pp_print_ty2 ff ty2 =
  match ty2 with
  | Ty2 (ty1s, ty) ->
      fprintf ff "%a@ -> %a"
      (Fmtutil.pp_print_delimited ~sep:pp_print_times pp_print_ty1_parens) ty1s
      pp_print_ty0 ty


(* {3 Typechecking} *)

exception Typechecking_error of ty0 * ty0
exception Typechecking_op_error of ty2 * ty2

let typecheck ~expected:ty01 ~actual:ty02 =
  if ty01 <> ty02 then begin
    raise (Typechecking_error (ty01, ty02))
  end

let typecheck_op ~expected:ty21 ~actual:ty22 =
  if ty21 <> ty22 then begin
    raise (Typechecking_op_error (ty21, ty22))
  end

let typecheck_error_mssg ~expected:ty01 ~actual:ty02 =
    Format.fprintf Format.str_formatter
    "expression is of type %a, expected type %a"
    pp_print_ty0 ty02
    pp_print_ty0 ty01;
    let mssg = Format.flush_str_formatter () in
    mssg

let typecheck_op_error_mssg ~expected:ty21 ~actual:ty22 =
    Format.fprintf Format.str_formatter
    "operator expression is of type %a, expected type %a"
    pp_print_ty2 ty22
    pp_print_ty2 ty21;
    let mssg = Format.flush_str_formatter () in
    mssg

