(*
 * encode/data.ml --- symbol data
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Type.T
open Util.Coll

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


(* {3 Types} *)

type smb_kind = Untyped | Typed | Special

type data =
  { dat_name  : string
  ; dat_ty2   : Type.T.ty2
  ; dat_kind  : smb_kind
  ; dat_tver  : tla_smb option
  }

type dep_data =
  { dat_deps  : tla_smb list
  ; dat_axms  : tla_axm list
  }


(* {3 Data} *)

let untyped_data tla_smb =
  begin match tla_smb with
  (* Logic *)
  | Choose ->
      ("Choose",        [ t_una t_idv (t_iob ()) ],           t_idv)
  (* Set Theory *)
  | Mem ->
      ("Mem",           [ t_cst t_idv ; t_cst t_idv ],        t_iob ())
  | SubsetEq ->
      ("SubsetEq",      [ t_cst t_idv ; t_cst t_idv ],        t_iob ())
  | SetEnum n ->
      ("SetEnum_" ^ string_of_int n,
                        List.init n (fun _ -> t_cst t_idv),   t_idv)
  | Union ->
      ("Union",         [ t_cst t_idv ],                      t_idv)
  | Subset ->
      ("Subset",        [ t_cst t_idv ],                      t_idv)
  | Cup ->
      ("Cup",           [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | Cap ->
      ("Cap",           [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | SetMinus ->
      ("SetMinus",      [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | SetSt ->
      ("SetSt",         [ t_cst t_idv ; t_una t_idv (t_iob ()) ],
                                                              t_idv)
  | SetOf n ->
      ("SetOf_" ^ string_of_int n,
                        List.init n (fun _ -> t_cst t_idv)
                        @ [ Ty1 (List.init n (fun _ -> t_idv), t_idv) ],
                                                              t_idv)
  (* Booleans *)
  | BoolSet ->
      ("BoolSet",       [],                                   t_idv)
  (* Strings *)
  | StrSet ->
      ("StrSet",        [],                                   t_idv)
  | StrLit str ->
      ("StrLit_" ^ str,
                        [],                                   t_idv)
  (* Arithmetic *)
  | IntSet ->
      ("IntSet",        [],                                   t_idv)
  | NatSet ->
      ("NatSet",        [],                                   t_idv)
  | IntLit n ->
      ("IntLit_" ^ string_of_int n,
                        [],                                   t_idv)
  | IntPlus ->
      ("Plus",       [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | IntUminus ->
      ("Uminus",     [ t_cst t_idv ],                      t_idv)
  | IntMinus ->
      ("Minus",      [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | IntTimes ->
      ("Times",      [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | IntQuotient ->
      ("Quotient",   [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | IntRemainder ->
      ("Remainder",  [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | IntExp ->
      ("Exp",        [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | IntLteq ->
      ("Lteq",       [ t_cst t_idv ; t_cst t_idv ],        t_iob ())
  | IntLt ->
      ("Lt",         [ t_cst t_idv ; t_cst t_idv ],        t_iob ())
  | IntGteq ->
      ("Gteq",       [ t_cst t_idv ; t_cst t_idv ],        t_iob ())
  | IntGt ->
      ("Gt",         [ t_cst t_idv ; t_cst t_idv ],        t_iob ())
  | IntRange ->
      ("Range",      [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  (* Functions *)
  | FunIsafcn ->
      ("FunIsafcn",     [ t_cst t_idv ],                      t_bol)
  | FunSet ->
      ("FunSet",        [],                                   t_idv)
  | FunConstr ->
      ("FunFcn",        [ t_cst t_idv ; t_una t_idv t_idv ],  t_idv)
  | FunDom ->
      ("FunDom",        [ t_cst t_idv ],                      t_idv)
  | FunApp ->
      ("FunApp",        [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | _ ->
      Errors.bug "Bad argument"
  end

let typed_data tla_smb =
  begin match tla_smb with
  | TIntPlus ->
      ("Plus_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_int,
      IntPlus)
  | TIntUminus ->
      ("Uminus_" ^ ty_to_string t_int,
                        [ t_cst t_int ],                      t_int,
      IntUminus)
  | TIntMinus ->
      ("Minus_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_int,
      IntMinus)
  | TIntTimes ->
      ("Times_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_int,
      IntTimes)
  | TIntQuotient ->
      ("Quotient_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_int,
      IntQuotient)
  | TIntRemainder ->
      ("Remainder_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_int,
      IntRemainder)
  | TIntExp ->
      ("Exp_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_int,
      IntExp)
  | TIntLteq ->
      ("Lteq_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_bol,
      IntLteq)
  | TIntLt ->
      ("Lt_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_bol,
      IntLt)
  | TIntGteq ->
      ("Gteq_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_bol,
      IntGteq)
  | TIntGt ->
      ("Gt_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_bol,
      IntGt)
  | TIntRange ->
      ("Range_" ^ ty_to_string t_int,
                        [ t_cst t_int ; t_cst t_int ],        t_idv,
      IntRange)
  | _ ->
      Errors.bug "Bad argument"
  end

let special_data tla_smb =
  begin match tla_smb with
  | Cast ty ->
      ("Cast_" ^ ty_to_string ty,
                        [ t_cst ty ],                         t_idv)
  | True ty ->
      ("Tt_" ^ ty_to_string ty,
                        [],                                   ty)
  | _ ->
      Errors.bug "Bad argument"
  end

let get_data tla_smb =
  match tla_smb with
  | Choose | Mem | SubsetEq | SetEnum _ | Union | Subset | Cup | Cap | SetMinus
  | SetSt | SetOf _ | BoolSet | StrSet | StrLit _ | IntSet | NatSet | IntLit _
  | IntPlus | IntUminus | IntMinus | IntTimes | IntQuotient | IntRemainder
  | IntExp | IntLteq | IntLt | IntGteq | IntGt | IntRange | FunIsafcn | FunSet
  | FunConstr | FunDom | FunApp ->
      let (nm, tins, tout) = untyped_data tla_smb in
      { dat_name = nm
      ; dat_ty2  = Ty2 (tins, tout)
      ; dat_kind = Untyped
      ; dat_tver = None
      }
  | TIntPlus | TIntUminus | TIntMinus | TIntTimes | TIntQuotient | TIntRemainder
  | TIntExp | TIntLteq | TIntLt | TIntGteq | TIntGt | TIntRange ->
      let (nm, tins, tout, tver) = typed_data tla_smb in
      { dat_name = nm
      ; dat_ty2  = Ty2 (tins, tout)
      ; dat_kind = Typed
      ; dat_tver = Some tver
      }
  | Cast _ | True _ ->
      let (nm, tins, tout) = special_data tla_smb in
      { dat_name = nm
      ; dat_ty2  = Ty2 (tins, tout)
      ; dat_kind = Special
      ; dat_tver = None
      }


(* {3 Dependencies} *)

type s =
  { declared_strlits : Ss.t
  ; declared_intlits : Is.t
  }

let init =
  { declared_strlits = Ss.empty
  ; declared_intlits = Is.empty
  }

let untyped_deps tla_smb s =
  let s' =
    match tla_smb with
    | _ -> s
  in
  begin match tla_smb with
  (* Logic *)
  | Choose ->
      ([], [ ChooseDef ; ChooseExt ])
  (* Set Theory *)
  | Mem ->
      ([], [ SetExt ])
  | SubsetEq ->
      ([ Mem ], [ SubsetEqDef ])
  | SetEnum n ->
      ([ Mem ], [ EnumDef n ])
  | Union ->
      ([ Mem ], [ UnionDef ])
  | Subset ->
      ([ Mem ], [ SubsetDef ])
  | Cup ->
      ([ Mem ], [ CupDef ])
  | Cap ->
      ([ Mem ], [ CapDef ])
  | SetMinus ->
      ([ Mem ], [ SetMinusDef ])
  | SetSt ->
      ([ Mem ], [ SetStDef ])
  | SetOf n ->
      ([ Mem ], [ SetOfDef n ])
  (* Booleans *)
  | BoolSet ->
      ([ Cast t_bol ], [ BoolSetDef ])
  (* Strings *)
  | StrSet ->
      ([ Cast t_str ], [ StrSetDef ])
  | StrLit str ->
      ([ Cast t_str ],   Ss.fold (fun str' -> List.cons (StrLitDistinct (str, str'))) s.declared_strlits [])
  (* Arithmetic *)
  | IntSet ->
      ([ Cast t_int ], [ IntSetDef ])
  | NatSet ->
      ([ Cast t_int ], [ NatSetDef ])
  | IntLit n ->
      ([],               Is.fold (fun n' -> List.cons (IntLitDistinct (n, n'))) s.declared_intlits [])
  | IntPlus ->
      ([ TIntPlus ; Cast t_int ], [ Typing TIntPlus ])
  | IntUminus ->
      ([ TIntUminus ; Cast t_int ], [ Typing TIntUminus ])
  | IntMinus ->
      ([ TIntMinus ; Cast t_int ], [ Typing TIntMinus ])
  | IntTimes ->
      ([ TIntTimes ; Cast t_int ], [ Typing TIntTimes ])
  | IntQuotient ->
      ([ TIntQuotient ; Cast t_int ], [ Typing TIntQuotient ])
  | IntRemainder ->
      ([ TIntRemainder ; Cast t_int ], [ Typing TIntRemainder ])
  | IntExp ->
      ([ TIntExp ; Cast t_int ], [ Typing TIntExp ])
  | IntLteq ->
      ([ TIntLteq ; Cast t_int ], [ Typing TIntLteq ])
  | IntLt ->
      ([ TIntLt ; Cast t_int ], [ Typing TIntLt ])
  | IntGteq ->
      ([ TIntGteq ; Cast t_int ], [ Typing TIntGteq ])
  | IntGt ->
      ([ TIntGt ; Cast t_int ], [ Typing TIntGt ])
  | IntRange ->
      ([ TIntRange ; Cast t_int ], [ Typing TIntRange ])
  (* Functions *)
  | FunIsafcn ->
      ([], [ FunExt ])
  | FunSet ->
      ([ Mem ; FunIsafcn ; FunDom ; FunApp ], [ FunSetDef ])
  | FunConstr ->
      ([ FunIsafcn ], [ FunConstrIsafcn ])
  | FunDom ->
      ([ FunConstr ], [ FunDomDef ])
  | FunApp ->
      ([ FunConstr ], [ FunAppDef ])
  | _ ->
      Errors.bug "Bad argument"
  end |>
  fun x -> (s', x)

let typed_deps tla_smb =
  begin match tla_smb with
  | TIntPlus ->
      ([], [])
  | TIntUminus ->
      ([], [])
  | TIntMinus ->
      ([], [])
  | TIntTimes ->
      ([], [])
  | TIntQuotient ->
      ([], [])
  | TIntRemainder ->
      ([], [])
  | TIntExp ->
      ([], [])
  | TIntLteq ->
      ([], [])
  | TIntLt ->
      ([], [])
  | TIntGteq ->
      ([], [])
  | TIntGt ->
      ([], [])
  | TIntRange ->
      ([], [])
  | _ ->
      Errors.bug "Bad argument"
  end |>
  fun x -> (fun s -> (s, x))

let special_deps tla_smb =
  begin match tla_smb with
  | Cast ty ->
      ([], [])
  | True ty ->
      ([], [])
  | _ ->
      Errors.bug "Bad argument"
  end |>
  fun x -> (fun s -> (s, x))

let get_deps tla_smb s =
  match tla_smb with
  | Choose | Mem | SubsetEq | SetEnum _ | Union | Subset | Cup | Cap | SetMinus
  | SetSt | SetOf _ | BoolSet | StrSet | StrLit _ | IntSet | NatSet | IntLit _
  | IntPlus | IntUminus | IntMinus | IntTimes | IntQuotient | IntRemainder
  | IntExp | IntLteq | IntLt | IntGteq | IntGt | IntRange | FunIsafcn | FunSet
  | FunConstr | FunDom | FunApp ->
      let s, (smbs, axms) = untyped_deps tla_smb s in
      s,
      { dat_deps = smbs
      ; dat_axms = axms
      }
  | TIntPlus | TIntUminus | TIntMinus | TIntTimes | TIntQuotient | TIntRemainder
  | TIntExp | TIntLteq | TIntLt | TIntGteq | TIntGt | TIntRange ->
      let s, (smbs, axms) = typed_deps tla_smb s in
      s,
      { dat_deps = smbs
      ; dat_axms = axms
      }
  | Cast _ | True _ ->
      let s, (smbs, axms) = special_deps tla_smb s in
      s,
      { dat_deps = smbs
      ; dat_axms = axms
      }


(* {3 Axioms} *)

let get_axm = function
  | _ -> Property.(%%) (Expr.T.Internal Builtin.TRUE) [] (* FIXME *)

