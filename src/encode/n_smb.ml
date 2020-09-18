(*
 * encode/smb.ml --- symbols for expressions in standard form
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Type.T
open Ext
open Property


(* {3 Symbols} *)

type 'a smb =
  { smb_name : string
  ; smb_ty2  : ty2
  ; smb_defn : 'a
  }

let mk_smb nm ty2 a =
  { smb_name = nm
  ; smb_ty2 = ty2
  ; smb_defn = a
  }

let get_name smb = smb.smb_name
let get_ty2 smb = smb.smb_ty2
let get_ty1 smb = downcast_ty1 smb.smb_ty2
let get_ty0 smb = downcast_ty0 (downcast_ty1 smb.smb_ty2)
let get_defn smb = smb.smb_defn

let get_ord smb =
  let ty2 = smb.smb_ty2 in
  match safe_downcast_ty1 ty2 with
  | None -> 2
  | Some ty1 ->
      match safe_downcast_ty0 ty1 with
      | None -> 1
      | Some _ -> 0


(* {3 Operations} *)

let fold f b smb =
  f b (get_defn smb)

let map f smb =
  let nm = get_name smb in
  let ty = get_ty2 smb in
  let a = get_defn smb in
  mk_smb nm ty (f a)

let iter f smb =
  f (get_defn smb)


(* {3 Pretty-printing} *)

let pp_print_smb ?pp_print_defn ff smb =
  let pp_print_defn ff defn =
    Option.iter (fun f -> Format.fprintf ff " := %a" f defn) pp_print_defn
  in
  Format.fprintf ff "{ %s : %a%a }"
  (get_name smb)
  pp_print_ty2 (get_ty2 smb)
  pp_print_defn (get_defn smb)

