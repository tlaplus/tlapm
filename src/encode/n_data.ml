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
  (*Errors.bug ?at mssg*)
  failwith mssg

let t_idv = TAtm TAIdv
let t_bol = TAtm TABol
let t_int = TAtm TAInt
let t_str = TAtm TAStr

let t_iob () = if !Params.enc_nobool then t_idv else t_bol

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
      ("StrLit_" ^ str, [],                                   t_idv)
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
      ("FunSet",        [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | FunConstr ->
      ("FunFcn",        [ t_cst t_idv ; t_una t_idv t_idv ],  t_idv)
  | FunDom ->
      ("FunDom",        [ t_cst t_idv ],                      t_idv)
  | FunApp ->
      ("FunApp",        [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | _ ->
      error "Bad argument"
  end

let typed_data tla_smb =
  begin match tla_smb with
  (* Strings *)
  | TStrLit str ->
      ("TStrLit_" ^ str,
                        [],                                   t_str,
      StrLit str)
  (* Arithmetic *)
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
      error "Bad argument"
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
      error "Bad argument"
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
  | TStrLit _ | TIntPlus | TIntUminus | TIntMinus | TIntTimes | TIntQuotient
  | TIntRemainder | TIntExp | TIntLteq | TIntLt | TIntGteq | TIntGt | TIntRange ->
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
  { strlits : Ss.t
  ; intlits : Is.t
  ; t_strlits : Ss.t
  }

let init =
  { strlits = Ss.empty
  ; intlits = Is.empty
  ; t_strlits = Ss.empty
  }

let untyped_deps tla_smb s =
  let s' =
    match tla_smb with
    | StrLit str ->
        { s with strlits = Ss.add str s.strlits }
    | IntLit n ->
        { s with intlits = Is.add n s.intlits }
    | _ -> s
  in
  begin match tla_smb with
  (* Logic *)
  | Choose ->
      ([], [ ChooseDef (*; ChooseExt*) ])
  (* Set Theory *)
  | Mem ->
      ([],        [ (*SetExt*) ])
  | SubsetEq ->
      ([ Mem ],   [ SubsetEqDef ])
  | SetEnum n ->
      ([ Mem ],   [ EnumDef n ])
  | Union ->
      ([ Mem ],   [ UnionDef ])
  | Subset ->
      ([ Mem ],   [ SubsetDef ])
  | Cup ->
      ([ Mem ],   [ CupDef ])
  | Cap ->
      ([ Mem ],   [ CapDef ])
  | SetMinus ->
      ([ Mem ],   [ SetMinusDef ])
  | SetSt ->
      ([ Mem ],   [ SetStDef ])
  | SetOf n ->
      ([ Mem ],   [ SetOfDef n ])
  (* Booleans *)
  | BoolSet ->
      ([], [])
  (* Strings *)
  | StrSet ->
      ([], [])
  | StrLit str ->
      let distincts =
        Ss.fold (fun str2 -> List.cons (StrLitDistinct (str, str2))) s.strlits []
      in
      ([ Mem ; StrSet ],                      [ StrLitIsstr str ] @ distincts)
  (* Arithmetic *)
  | IntSet ->
      ([], [])
  | NatSet ->
      ([ IntSet ; IntLit 0 ; IntLteq ],       [ NatSetDef ])
  | IntLit n ->
      let distincts =
        Is.fold (fun m -> List.cons (IntLitDistinct (m, n))) s.intlits []
      in
      ([ Mem ; IntSet ],                      [ IntLitIsint n ] @ distincts)
  | IntPlus when !Params.enc_noarith ->
      ([ Mem ; IntSet ],                      [ IntPlusTyping ])
  | IntUminus when !Params.enc_noarith ->
      ([ Mem ; IntSet ],                      [ IntUminusTyping ])
  | IntMinus when !Params.enc_noarith ->
      ([ Mem ; IntSet ],                      [ IntMinusTyping ])
  | IntTimes when !Params.enc_noarith ->
      ([ Mem ; IntSet ],                      [ IntTimesTyping ])
  | IntQuotient when !Params.enc_noarith ->
      ([ Mem ; IntSet ; IntLteq ; IntLit 0 ], [ IntQuotientTyping ])
  | IntRemainder when !Params.enc_noarith ->
      ([ Mem ; IntSet ; IntLteq ; IntLit 0 ; IntLit 1 ;
          IntRange ; IntMinus ],              [ IntRemainderTyping ])
  | IntExp when !Params.enc_noarith ->
      ([ Mem ; IntSet ; IntLit 0 ],           [ IntExpTyping ])
  | IntLteq | IntLt | IntGteq | IntGt when !Params.enc_noarith ->
      ([], [])
  | IntPlus ->
      ([ Cast (TAtm TAInt) ; TIntPlus ],      [ Typing TIntPlus ])
  | IntUminus ->
      ([ Cast (TAtm TAInt) ; TIntUminus ],    [ Typing TIntUminus ])
  | IntMinus ->
      ([ Cast (TAtm TAInt) ; TIntMinus ],     [ Typing TIntMinus ])
  | IntTimes ->
      ([ Cast (TAtm TAInt) ; TIntTimes ],     [ Typing TIntTimes ])
  | IntQuotient ->
      ([ Cast (TAtm TAInt) ; TIntQuotient ],  [ Typing TIntQuotient ])
  | IntRemainder ->
      ([ Cast (TAtm TAInt) ; TIntRemainder ], [ Typing TIntRemainder ])
  | IntExp ->
      ([ Cast (TAtm TAInt) ; TIntExp ],       [ Typing TIntExp ])
  | IntLteq ->
      ([ Cast (TAtm TAInt) ; TIntLteq ],      [ Typing TIntLteq ])
  | IntLt ->
      ([ Cast (TAtm TAInt) ; TIntLt ],        [ Typing TIntLt ])
  | IntGteq ->
      ([ Cast (TAtm TAInt) ; TIntGteq ],      [ Typing TIntGteq ])
  | IntGt ->
      ([ Cast (TAtm TAInt) ; TIntGt ],        [ Typing TIntGt ])
  | IntRange ->
      ([ Mem ; IntSet ; IntLteq ],            [ IntRangeDef ])
  (* Functions *)
  | FunIsafcn ->
      ([ (*FunDom ; FunConstr ; FunApp*) ],
                                  [ (*FunExt*) ])
  | FunSet ->
      ([ Mem ; FunIsafcn ; FunDom ; FunApp ],
                                  [ FunSetDef ])
  | FunConstr ->
      ([ FunIsafcn ],             [ FunConstrIsafcn ])
  | FunDom ->
      ([ FunConstr ],             [ FunDomDef ])
  | FunApp ->
      ([ FunConstr ],             [ FunAppDef ])
  | _ ->
      error "Bad argument"
  end |>
  fun x -> (s', x)

let typed_deps tla_smb s =
  let s' =
    match tla_smb with
    | TStrLit str ->
        { s with t_strlits = Ss.add str s.t_strlits }
    | _ -> s
  in
  begin match tla_smb with
  (* Strings *)
  | TStrLit str ->
      let distincts =
        Ss.fold (fun str2 -> List.cons (TStrLitDistinct (str, str2))) s.t_strlits []
      in
      ([], distincts)
  (* Arithmetic *)
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
  | TIntGt ->
      (* Implemented natively in most solvers *)
      ([], [])
  | TIntRange ->
      ([], [])
  | _ ->
      error "Bad argument"
  end |>
  fun x -> (s', x)

let special_deps tla_smb =
  begin match tla_smb with
  | Cast ty0 ->
      let tla_smbs =
        match ty0 with
        | TAtm TAIdv -> []
        | TAtm TABol -> [ Mem ; BoolSet ; True (TAtm TAIdv) ]
        | TAtm TAInt -> [ Mem ; IntSet ]
        | TAtm TAStr -> [ Mem ; StrSet ]
        | _ -> []
      in
      (tla_smbs, [ CastInj ty0 ; TypeGuard ty0 ])
  | True ty0 ->
      ([], [])
  | _ ->
      error "Bad argument"
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
  | TStrLit _ | TIntPlus | TIntUminus | TIntMinus | TIntTimes | TIntQuotient
  | TIntRemainder | TIntExp | TIntLteq | TIntLt | TIntGteq | TIntGt
  | TIntRange ->
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

