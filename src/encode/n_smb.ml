(*
 * encode/smb.ml --- symbols for expressions in standard form
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
 *)

open Type.T
open Ext
open Property

open N_table
open N_data


(* {3 Symbols} *)

type smb_kind = N_data.smb_kind

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

let mk_smb tla_smb =
  let dat = get_data tla_smb in
  { smb_name = dat.dat_name
  ; smb_ty2 = dat.dat_ty2
  ; smb_smb = tla_smb
  ; smb_kind = dat.dat_kind
  ; smb_tver = dat.dat_tver
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

