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
  let d = ord k in
  if d < 0 || d > 2 then
    let mssg = ("Attempt to create symbol '" ^ nm ^ "' \
                of order " ^ string_of_int d) in
    Errors.bug mssg
  else
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

module OrdSmb = struct
  type t = smb
  let compare = Pervasives.compare (* TODO *)
end

module SmbSet = Set.Make (OrdSmb)


(* {3 Versions} *)

(* Replace every type with U, except positive occurrences of Bool *)
let u_kind k =
  let rec u_kind_pos (TKind (ks, ty)) =
    let ks = List.map u_kind_neg ks in
    let ty =
      match ty with
      | TAtom TBool -> ty_bool
      | _ -> ty_u
    in
    TKind (ks, ty)
  and u_kind_neg (TKind (ks, ty)) =
    let ks = List.map u_kind_pos ks in
    TKind (ks, ty_u)
  in
  u_kind_pos k

let u_smb smb =
  { smb with
    smb_name = smb.smb_name ^ "_U"
  ; smb_kind = u_kind smb.smb_kind
  }


(* {3 Table} *)

let suffix s ss = String.concat "__" (s :: ss)

let rec type_to_string ty =
    match ty with
    | TUnknown -> "Unknown"
    | TVar a -> "Var" ^ a
    | TAtom TU -> "U"
    | TAtom TBool -> "Bool"
    | TAtom TInt -> "Int"
    | TAtom TReal -> "Real"
    | TAtom TStr -> "String"
    | TSet ty ->
        let s = type_to_string ty in
        "Set" ^ s
    | TArrow (ty1, ty2) ->
        let s1 = type_to_string ty1 in
        let s2 = type_to_string ty2 in
        "Arrow" ^ s1 ^ s2
    | TProd tys ->
        let ss = List.map type_to_string tys in
        List.fold_left (^) "Prod" ss

let choose ty =
  let id = suffix "Choose" [ type_to_string ty ] in
  mk_snd_smb Logic id [ ([ty], ty_bool) ] ty

let mem ty =
  let id = suffix "Mem" [ type_to_string ty ] in
  mk_fst_smb Sets id [ ty ; TSet ty ] ty_bool
let subseteq ty =
  let id = suffix "Subseteq" [ type_to_string ty ] in
  mk_fst_smb Sets id [ TSet ty ; TSet ty ] ty_bool
let setenum n ty =
  let id = suffix "SetEnum" [ string_of_int n ; type_to_string ty ] in
  mk_fst_smb Sets id (List.init n (fun _ -> ty)) (TSet ty)
let union ty =
  let id = suffix "Union" [ type_to_string ty ] in
  mk_fst_smb Sets id [ TSet (TSet ty) ] (TSet ty)
let subset ty =
  let id = suffix "Subset" [ type_to_string ty ] in
  mk_fst_smb Sets id [ TSet ty ] (TSet (TSet ty))
let cup ty =
  let id = suffix "Cup" [ type_to_string ty ] in
  mk_fst_smb Sets id [ TSet ty ; TSet ty ] (TSet ty)
let cap ty =
  let id = suffix "Cap" [ type_to_string ty ] in
  mk_fst_smb Sets id [ TSet ty ; TSet ty ] (TSet ty)
let setminus ty =
  let id = suffix "Setminus" [ type_to_string ty ] in
  mk_fst_smb Sets id [ TSet ty ; TSet ty ] (TSet ty)
let setst ty =
  let id = suffix "SetSt" [ type_to_string ty ] in
  mk_snd_smb Sets id [ ([], TSet ty) ; ([ty], ty_bool) ] (TSet ty)
let setof tys ty =
  let id = suffix "SetOf" (List.map type_to_string tys @ [ type_to_string ty ]) in
  mk_snd_smb Sets id ( (tys, ty) :: List.map (fun ty -> ([], TSet ty)) tys ) (TSet ty)

let set_boolean =
  let id = "Boolean" in
  mk_cst_smb Booleans id (TSet ty_bool)
let set_string =
  let id = "String" in
  mk_cst_smb Strings id (TSet ty_str)
let set_int =
  let id = "Int" in
  mk_cst_smb Arithmetic id (TSet ty_int)
let set_nat =
  let id = "Nat" in
  mk_cst_smb Arithmetic id (TSet ty_int)
let set_real =
  let id = "Real" in
  mk_cst_smb Arithmetic id (TSet ty_real)

let arrow ty1 ty2 =
  let id = suffix "Arrow" [ type_to_string ty1 ; type_to_string ty2 ] in
  mk_fst_smb Functions id [ TSet ty1 ; TSet ty2 ] (TSet (TArrow (ty1, ty2)))
let domain ty1 ty2 =
  let id = suffix "Domain" [ type_to_string ty1 ; type_to_string ty2 ] in
  mk_fst_smb Functions id [ TArrow (ty1, ty2) ] (TSet ty1)
let fcnapp ty1 ty2 =
  let id = suffix "FcnApp" [ type_to_string ty1 ; type_to_string ty2 ] in
  mk_fst_smb Functions id [ TArrow (ty1, ty2) ; ty1 ] ty2
let fcn ty1 ty2 =
  let id = suffix "Fcn" [ type_to_string ty1 ; type_to_string ty2 ] in
  mk_snd_smb Functions id [ ([], TSet ty1) ; ([ty1], ty2) ] (TArrow (ty1, ty2))
let except ty1 ty2 =
  let id = suffix "Except" [ type_to_string ty1 ; type_to_string ty2 ] in
  mk_fst_smb Functions id [ TArrow (ty1, ty2) ; ty1 ; ty2 ] (TArrow (ty1, ty2))

let product tys =
  let id = suffix "Product" (List.map type_to_string tys) in
  mk_fst_smb Tuples id tys (TSet (TProd tys))
let tuple tys =
  let id = suffix "Tuple" (List.map type_to_string tys) in
  mk_fst_smb Tuples id tys (TProd tys)
