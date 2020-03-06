(*
 * encode/table.ml --- table of symbols used to encode POs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Type.T
open Property


(* {3 Symbols} *)

type family =
  | Logic
  | Sets
  | Booleans
  | Strings
  | Tuples
  | Functions
  | Records
  | Sequences
  | Arithmetic
  | Special

type smb =
  { smb_fam  : family
  ; smb_name : string
  ; smb_kind : ty_kind
  ; smb_ord  : int
  }

let mk_smb fam nm k =
  { smb_fam = fam
  ; smb_name = nm
  ; smb_kind = k
  ; smb_ord = ord k
  }

let mk_snd_smb fam nm ints outt =
  let ks =
    List.map begin fun (tys, ty) ->
      mk_fstk_ty tys ty
    end ints
  in
  let k = mk_kind_ty ks outt in
  mk_smb fam nm k

let mk_fst_smb fam nm ints outt =
  let k = mk_fstk_ty ints outt in
  mk_smb fam nm k

let mk_cst_smb fam nm ty =
  let k = mk_cstk_ty ty in
  mk_smb fam nm k

let get_fam smb = smb.smb_fam
let get_name smb = smb.smb_name
let get_kind smb = smb.smb_kind
let get_ord smb = smb.smb_ord

let rec u_kind (TKind (ks, ty)) =
  TKind (List.map u_kind ks, ty_u)

let u_smb smb =
  { smb with
    smb_name = smb.smb_name ^ "_U"
  ; smb_kind = u_kind smb.smb_kind
  }


(* {3 Table} *)

(* TODO give unique name to each specialized smb *)

let choose ty =
  mk_snd_smb Logic "Choose" [ ([ty], ty_bool) ] ty

let mem ty =
  mk_fst_smb Sets "Mem" [ ty ; TSet ty ] ty_bool
let subseteq ty =
  mk_fst_smb Sets "Subseteq" [ TSet ty ; TSet ty ] ty_bool
let setenum n ty =
  mk_fst_smb Sets "SetEnum" (List.init n (fun _ -> ty)) (TSet ty)
let union ty =
  mk_fst_smb Sets "Union" [ TSet (TSet ty) ] (TSet ty)
let subset ty =
  mk_fst_smb Sets "Subset" [ TSet ty ] (TSet (TSet ty))
let cup ty =
  mk_fst_smb Sets "Cup" [ TSet ty ; TSet ty ] (TSet ty)
let cap ty =
  mk_fst_smb Sets "Cap" [ TSet ty ; TSet ty ] (TSet ty)
let setminus ty =
  mk_fst_smb Sets "Setminus" [ TSet ty ; TSet ty ] (TSet ty)
let setst ty =
  mk_snd_smb Sets "SetSt" [ ([], TSet ty) ; ([ty], ty_bool) ] (TSet ty)
let setof tys ty =
  mk_snd_smb Sets "SetOf" ( (tys, ty) :: List.map (fun ty -> ([], TSet ty)) tys ) (TSet ty)

let set_boolean =
  mk_cst_smb Booleans "Boolean" (TSet ty_bool)
let set_string =
  mk_cst_smb Strings "String" (TSet ty_str)
let set_int =
  mk_cst_smb Arithmetic "Int" (TSet ty_int)
let set_nat =
  mk_cst_smb Arithmetic "Nat" (TSet ty_int)
let set_real =
  mk_cst_smb Arithmetic "Real" (TSet ty_real)

let arrow ty1 ty2 =
  mk_fst_smb Functions "Arrow" [ TSet ty1 ; TSet ty2 ] (TSet (TArrow (ty1, ty2)))
let domain ty1 ty2 =
  mk_fst_smb Functions "Domain" [ TArrow (ty1, ty2) ] (TSet ty1)
let fcnapp ty1 ty2 =
  mk_fst_smb Functions "FcnApp" [ TArrow (ty1, ty2) ; ty1 ] ty2
let fcn ty1 ty2 =
  mk_snd_smb Functions "Fcn" [ ([], TSet ty1) ; ([ty1], ty2) ] (TArrow (ty1, ty2))
let except ty1 ty2 =
  mk_fst_smb Functions "Except" [ TArrow (ty1, ty2) ; ty1 ; ty2 ] (TArrow (ty1, ty2))

let product tys =
  mk_fst_smb Tuples "Product" tys (TSet (TProd tys))
let tuple tys =
  mk_fst_smb Tuples "Tuple" tys (TProd tys)
