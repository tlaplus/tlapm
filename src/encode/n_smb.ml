(*
 * encode/smb.ml --- symbols for expressions in standard form
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Type.T
open Ext
open Property

open N_table
open N_data


(* {3 Symbols} *)

type smb_kind = Untyped | Typed | Special

type smb =
  { smb_name  : string
  ; smb_ty2   : ty2
  ; smb_smb   : tla_smb
  ; smb_kind  : smb_kind
  ; smb_tver  : tla_smb option
  }

let smb_prop = make "Encode.Smb.smb_prop"

module SmbOrd = struct
  type t = smb
  let compare smb1 smb2 =
    Pervasives.compare smb1.smb_name smb2.smb_name
end

module SmbSet = Set.Make (SmbOrd)

type s = N_data.s
let init = N_data.init

let mk_smb s ?tver tla_smb =
  let s, dat = get_data s tla_smb in
  let tver =
    match tver, dat.dat_kind with
    | None, Typed -> raise (Invalid_argument "smb with typed version is already typed")
    | _, _ -> tver
  in
  let kind =
    match dat.dat_kind with
    (* Conversion *)
    | Untyped -> Untyped
    | Typed -> Typed
    | Special -> Special
  in
  s,
  { smb_name = dat.dat_name
  ; smb_ty2 = dat.dat_ty2
  ; smb_smb = tla_smb
  ; smb_kind = kind
  ; smb_tver = tver
  }

let equal_smb smb1 smb2 =
  smb1.smb_name = smb2.smb_name

let get_name smb = smb.smb_name
let get_ty2 smb = smb.smb_ty2
let get_ty1 smb = downcast_ty1 smb.smb_ty2
let get_ty0 smb = downcast_ty0 (downcast_ty1 smb.smb_ty2)

let get_defn smb  = smb.smb_smb
let get_kind smb  = smb.smb_kind
let get_tdefn smb = Option.get smb.smb_tver

let get_ord smb =
  let ty2 = smb.smb_ty2 in
  match safe_downcast_ty1 ty2 with
  | None -> 2
  | Some ty1 ->
      match safe_downcast_ty0 ty1 with
      | None -> 1
      | Some _ -> 0


(* {3 Pretty-printing} *)

let pp_print_smb ff smb =
  Format.fprintf ff "{ %s : %a }"
  (get_name smb)
  pp_print_ty2 (get_ty2 smb)

