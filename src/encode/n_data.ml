(*
 * encode/data.ml --- symbol data
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Type.T

open N_table


(* {3 Helpers} *)

let error ?at mssg =
  let mssg = "Encode.Data: " ^ mssg in
  Errors.bug ?at mssg

let t_idv = TAtm TAIdv
let t_bol = TAtm TABol
let t_int = TAtm TAInt
let t_str = TAtm TAStr

let t_iob () = if !Params.enc_typepreds then t_bol else t_idv

let t_cst ty = Ty1 ([], ty)
let t_una ty1 ty2 = Ty1 ([ ty1 ], ty2)
let t_bin ty1 ty2 ty3 = Ty1 ([ ty1 ; ty2 ], ty3)


(* {3 Main} *)

type smb_kind = Untyped | Typed | Special

type data =
  { dat_name  : string
  ; dat_ty2   : Type.T.ty2
  ; dat_deps  : tla_smb list
  ; dat_axms  : tla_axm list
  ; dat_kind  : smb_kind
  }

let untyped_data tla_smb =
  match tla_smb with
  (* Logic *)
  | Choose ->
      ("Choose",        [ t_una t_idv (t_iob ()) ],           t_idv,
      [], [ ChooseDef ; ChooseExt ])
  (* Set Theory *)
  | Mem ->
      ("Mem",           [ t_cst t_idv ; t_cst t_idv ],        t_iob (),
      [], [ SetExt ])
  | SubsetEq ->
      ("SubsetEq",      [ t_cst t_idv ; t_cst t_idv ],        t_iob (),
      [ Mem ], [ SubsetEqDef ])
  | SetEnum n ->
      ("SetEnum_" ^ string_of_int n,
                        List.init n (fun _ -> t_cst t_idv),   t_idv,
      [ Mem ], [ EnumDef n ])
  | Union ->
      ("Union",         [ t_cst t_idv ],                      t_idv,
      [ Mem ], [ UnionDef ])
  | Subset ->
      ("Subset",        [ t_cst t_idv ],                      t_idv,
      [ Mem ], [ SubsetDef ])
  | Cup ->
      ("Cup",           [ t_cst t_idv ; t_cst t_idv ],        t_idv,
      [ Mem ], [ CupDef ])
  | Cap ->
      ("Cap",           [ t_cst t_idv ; t_cst t_idv ],        t_idv,
      [ Mem ], [ CapDef ])
  | SetMinus ->
      ("SetMinus",      [ t_cst t_idv ; t_cst t_idv ],        t_idv,
      [ Mem ], [ SetMinusDef ])
  | SetSt ->
      ("SetSt",         [ t_cst t_idv ; t_una t_idv (t_iob ()) ],
                                                              t_idv,
      [ Mem ], [ SetStDef ])
  | SetOf n ->
      ("SetOf_" ^ string_of_int n,
                        List.init n (fun _ -> t_cst t_idv)
                        @ [ Ty1 (List.init n (fun _ -> t_idv), t_idv) ],
                                                              t_idv,
      [ Mem ], [ SetOfDef n ])
  (* Booleans *)
  | BoolSet ->
      ("BoolSet",       [],                                   t_idv,
      [ Cast t_bol ], [ BoolSetDef ])
  (* Strings *)
  | StrSet ->
      ("StrSet",        [],                                   t_idv,
      [ Cast t_str ], [ StrSetDef ])
  | StrLit s ->
      ("StrLit_" ^ s,
                        [],                                   t_idv,
      [ Cast t_str ], []) (* FIXME str distinct *)
  (* Arithmetic *)
  | IntSet ->
      ("IntSet",        [],                                   t_idv,
      [ Cast t_int ], [ IntSetDef ])
  | NatSet ->
      ("NatSet",        [],                                   t_idv,
      [ Cast t_int ], [ NatSetDef ])
  | IntPlus ->
      ("Plus",       [ t_cst t_idv ; t_cst t_idv ],        t_idv,
      [ TIntPlus ; Cast t_int ], [ Typing TIntPlus ])
  | IntUminus ->
      ("Uminus",     [ t_cst t_idv ],                      t_idv,
      [ TIntUminus ; Cast t_int ], [ Typing TIntUminus ])
  | IntMinus ->
      ("Minus",      [ t_cst t_idv ; t_cst t_idv ],        t_idv,
      [ TIntMinus ; Cast t_int ], [ Typing TIntMinus ])
  | IntTimes ->
      ("Times",      [ t_cst t_idv ; t_cst t_idv ],        t_idv,
      [ TIntTimes ; Cast t_int ], [ Typing TIntTimes ])
  | IntQuotient ->
      ("Quotient",   [ t_cst t_idv ; t_cst t_idv ],        t_idv,
      [ TIntQuotient ; Cast t_int ], [ Typing TIntQuotient ])
  | IntRemainder ->
      ("Remainder",  [ t_cst t_idv ; t_cst t_idv ],        t_idv,
      [ TIntRemainder ; Cast t_int ], [ Typing TIntRemainder ])
  | IntExp ->
      ("Exp",        [ t_cst t_idv ; t_cst t_idv ],        t_idv,
      [ TIntExp ; Cast t_int ], [ Typing TIntExp ])
  | IntLteq ->
      ("Lteq",       [ t_cst t_idv ; t_cst t_idv ],        t_iob (),
      [ TIntLteq ; Cast t_int ], [ Typing TIntLteq ])
  | IntLt ->
      ("Lt",         [ t_cst t_idv ; t_cst t_idv ],        t_iob (),
      [ TIntLt ; Cast t_int ], [ Typing TIntLt ])
  | IntGteq ->
      ("Gteq",       [ t_cst t_idv ; t_cst t_idv ],        t_iob (),
      [ TIntGteq ; Cast t_int ], [ Typing TIntGteq ])
  | IntGt ->
      ("Gt",         [ t_cst t_idv ; t_cst t_idv ],        t_iob (),
      [ TIntGt ; Cast t_int ], [ Typing TIntGt ])
  | IntRange ->
      ("Range",      [ t_cst t_idv ; t_cst t_idv ],        t_idv,
      [ TIntRange ; Cast t_int ], [ Typing TIntRange ])
  (* Functions *)
  | FunIsafcn ->
      ("FunIsafcn",     [ t_cst t_idv ],                      t_bol,
      [], [ FunExt ])
  | FunSet ->
      ("FunSet",        [],                                   t_idv,
      [ Mem ; FunIsafcn ; FunDom ; FunApp ], [ FunSetDef ])
  | FunConstr ->
      ("FunFcn",        [ t_cst t_idv ; t_una t_idv t_idv ],  t_idv,
      [ FunIsafcn ], [ FunConstrIsafcn ])
  | FunDom ->
      ("FunDom",        [ t_cst t_idv ],                      t_idv,
      [ FunConstr ], [ FunDomDef ])
  | FunApp ->
      ("FunApp",        [ t_cst t_idv ; t_cst t_idv ],        t_idv,
      [ FunConstr ], [ FunAppDef ])
  | _ ->
      Errors.bug "Bad argument"

let typed_data tla_smb =
  match tla_smb with
  | TIntPlus ->
      ("Plus_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_int,
      [], [])
  | TIntUminus ->
      ("Uminus_" ^ ty_to_string t_int,
                        [ t_cst t_int ],                      t_int,
      [], [])
  | TIntMinus ->
      ("Minus_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_int,
      [], [])
  | TIntTimes ->
      ("Times_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_int,
      [], [])
  | TIntQuotient ->
      ("Quotient_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_int,
      [], [])
  | TIntRemainder ->
      ("Remainder_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_int,
      [], [])
  | TIntExp ->
      ("Exp_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_int,
      [], [])
  | TIntLteq ->
      ("Lteq_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_bol,
      [], [])
  | TIntLt ->
      ("Lt_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_bol,
      [], [])
  | TIntGteq ->
      ("Gteq_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_bol,
      [], [])
  | TIntGt ->
      ("Gt_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_bol,
      [], [])
  | TIntRange ->
      ("Range_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_idv,
      [], [])
  | _ ->
      Errors.bug "Bad argument"

let special_data tla_smb =
  match tla_smb with
  | Cast ty ->
      ("Cast_" ^ ty_to_string ty,
                        [ t_cst ty ],                         t_idv,
      [], [])
  | True ty ->
      ("Tt_" ^ ty_to_string ty,
                        [],                                   ty,
      [], [])
  | _ ->
      Errors.bug "Bad argument"

let get_data tla_smb =
  match tla_smb with
  | Choose
  | Mem
  | SubsetEq
  | SetEnum _
  | Union
  | Subset
  | Cup
  | Cap
  | SetMinus
  | SetSt
  | SetOf _
  | BoolSet
  | StrSet
  | StrLit _
  | IntSet
  | NatSet
  | IntPlus
  | IntUminus
  | IntMinus
  | IntTimes
  | IntQuotient
  | IntRemainder
  | IntExp
  | IntLteq
  | IntLt
  | IntGteq
  | IntGt
  | IntRange
  | FunIsafcn
  | FunSet
  | FunConstr
  | FunDom
  | FunApp ->
      let nm, tins, tout, deps, axms = untyped_data tla_smb in
      { dat_name = nm
      ; dat_ty2 = Ty2 (tins, tout)
      ; dat_deps = deps
      ; dat_axms = axms
      ; dat_kind = Untyped
      }
  | TIntPlus
  | TIntUminus
  | TIntMinus
  | TIntTimes
  | TIntQuotient
  | TIntRemainder
  | TIntExp
  | TIntLteq
  | TIntLt
  | TIntGteq
  | TIntGt
  | TIntRange ->
      let nm, tins, tout, deps, axms = special_data tla_smb in
      { dat_name = nm
      ; dat_ty2 = Ty2 (tins, tout)
      ; dat_deps = deps
      ; dat_axms = axms
      ; dat_kind = Typed
      }
  | Cast _
  | True _ ->
      let nm, tins, tout, deps, axms = special_data tla_smb in
      { dat_name = nm
      ; dat_ty2 = Ty2 (tins, tout)
      ; dat_deps = deps
      ; dat_axms = axms
      ; dat_kind = Special
      }


let get_axm = function
  | _ -> error "Not implemented"

