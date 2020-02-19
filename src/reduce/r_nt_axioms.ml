(*
 * reduce/nt_axioms.ml --- axioms for notypes encoding
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Expr.T
open Type.T
open Property


(* {3 Identifiers} *)

let nt_prefix = "NT__"

let uany_nm = nt_prefix ^ "any_u"
let stringany_nm = nt_prefix ^ "any_string"
let mem_nm = nt_prefix ^ "mem"
let subseteq_nm = nt_prefix ^ "subseteq"
let empty_nm = nt_prefix ^ "Empty"
let enum_nm n = if n = 0 then empty_nm else nt_prefix ^ "Enum_" ^ string_of_int n
let union_nm = nt_prefix ^ "Union"
let power_nm = nt_prefix ^ "Power"
let cup_nm = nt_prefix ^ "cup"
let cap_nm = nt_prefix ^ "cap"
let setminus_nm = nt_prefix ^ "setminus"
let setst_nm s _ = nt_prefix ^ "SetSt_" ^ s
let boolean_nm = nt_prefix ^ "Boolean"
let booltou_nm = nt_prefix ^ "bool_to_u"
let string_nm = nt_prefix ^ "String"
let stringtou_nm = nt_prefix ^ "string_to_u"
let stringlit_nm s = nt_prefix ^ "string_lit_" ^ s


(* {3 Declarations} *)

let mk_fresh nm ss s =
  let ss = List.map mk_atom_ty ss in
  let s = mk_atom_ty s in
  let k = mk_fstk_ty ss s in
  let shp =
    let n = List.length ss in
    if n = 0 then Shape_expr
    else Shape_op n
  in
  Fresh (annot_kind (nm %% []) k, shp, Constant, Unbounded)

let uany_decl = mk_fresh uany_nm [] TU %% []
let stringany_decl = mk_fresh uany_nm [] TStr %% []
let mem_decl = mk_fresh mem_nm [ TU ; TU ] TBool %% []
let subseteq_decl = mk_fresh subseteq_nm [ TU ; TU ] TBool %% []
let empty_decl = mk_fresh empty_nm [] TU %% []
let enum_decl n = mk_fresh (enum_nm n) (List.init n (fun _ -> TU)) TU %% []
let union_decl = mk_fresh union_nm [ TU ] TU %% []
let power_decl = mk_fresh power_nm [ TU ] TU %% []
let cup_decl = mk_fresh cup_nm [ TU ; TU ] TU %% []
let cap_decl = mk_fresh cap_nm [ TU ; TU ] TU %% []
let setminus_decl = mk_fresh setminus_nm [ TU ; TU ] TU %% []
let boolean_decl = mk_fresh boolean_nm [] TU %% []
let booltou_decl = mk_fresh booltou_nm [ TBool ] TU %% []
let string_decl = mk_fresh string_nm [] TU %% []
let stringtou_decl = mk_fresh stringtou_nm [ TStr ] TU %% []
let stringlit_decl s = mk_fresh (stringlit_nm s) [] TStr %% []

let setst_decl s k =
  let ss =
    match k with
    | TKind (TKind ([], TAtom TU) :: ks, TAtom TBool) ->
        List.map (fun k -> get_atom (get_ty k)) ks
    | _ -> invalid_arg ("Reduce.NtAxioms.setst_decl: \
                        bad kind provided")
  in
  mk_fresh (setst_nm s k) (TU :: ss) TU %% []


(* {3 Axioms} *)
