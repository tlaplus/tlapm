(*
 * encode/data.ml --- symbol data
 *
 *
 * Copyright (C) 2022  INRIA and Microsoft Corporation
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

let t_fs s = TFSet s

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
      ("Choose",        [ t_una t_idv t_bol ],                t_idv)
  (* Set Theory *)
  | Mem ->
      ("Mem",           [ t_cst t_idv ; t_cst t_idv ],        t_bol)
  | SubsetEq ->
      ("SubsetEq",      [ t_cst t_idv ; t_cst t_idv ],        t_bol)
  | SetEnum n ->
      ("SetEnum_" ^ string_of_int n,
                        List.init n (fun _ -> t_cst t_idv),   t_idv)
  | Add ->
      ("Add",           [ t_cst t_idv ],                      t_idv)
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
      ("SetSt",         [ t_cst t_idv ; t_una t_idv t_bol ],
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
      ("IntPlus",       [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | IntUminus ->
      ("IntUminus",     [ t_cst t_idv ],                      t_idv)
  | IntMinus ->
      ("IntMinus",      [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | IntTimes ->
      ("IntTimes",      [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | IntQuotient ->
      ("IntQuotient",   [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | IntRemainder ->
      ("IntRemainder",  [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | IntExp ->
      ("IntExp",        [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | IntLteq ->
      ("IntLteq",       [ t_cst t_idv ; t_cst t_idv ],        t_bol)
  | IntLt ->
      ("IntLt",         [ t_cst t_idv ; t_cst t_idv ],        t_bol)
  | IntGteq ->
      ("IntGteq",       [ t_cst t_idv ; t_cst t_idv ],        t_bol)
  | IntGt ->
      ("IntGt",         [ t_cst t_idv ; t_cst t_idv ],        t_bol)
  | IntRange ->
      ("IntRange",      [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  (* Functions *)
  | FunIsafcn ->
      ("FunIsafcn",     [ t_cst t_idv ],                      t_bol)
  | FunSet ->
      ("FunSet",        [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | FunConstr ->
      ("FunFcn",        [ t_cst t_idv ; t_una t_idv t_idv ],  t_idv)
  | FunDom ->
      ("FunDom",        [ t_cst t_idv ],                      t_idv)
  | FunIm ->
      ("FunIm",         [ t_cst t_idv ],                      t_idv)
  | FunApp ->
      ("FunApp",        [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | FunExcept ->
      ("FunExcept",     [ t_cst t_idv ; t_cst t_idv ; t_cst t_idv ],
                                                              t_idv)
  (* Tuples *)
  | Tuple n ->
      ("Tuple_" ^ string_of_int n,
                        List.init n (fun _ -> t_cst t_idv),   t_idv)
  | Product n ->
      ("Product_" ^ string_of_int n,
                        List.init n (fun _ -> t_cst t_idv),   t_idv)
  (* Records *)
  | Rec fs ->
      let n = List.length fs in
      (List.fold_left (fun s1 s2 -> s1 ^ "_" ^ s2) "Record" fs,
                        List.init n (fun _ -> t_cst t_idv),   t_idv)
  | RecSet fs ->
      let n = List.length fs in
      (List.fold_left (fun s1 s2 -> s1 ^ "_" ^ s2) "RecordSet" fs,
                        List.init n (fun _ -> t_cst t_idv),   t_idv)
  (* Sequences *)
  | SeqSeq ->
      ("Seq",           [ t_cst t_idv ],                      t_idv)
  | SeqLen ->
      ("Len",           [ t_cst t_idv ],                      t_idv)
  | SeqBSeq ->
      ("BSeq",          [ t_cst t_idv ],                      t_idv)
  | SeqCat ->
      ("Cat",           [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | SeqAppend ->
      ("Append",        [ t_cst t_idv ; t_cst t_idv ],        t_idv)
  | SeqHead ->
      ("Head",          [ t_cst t_idv ],                      t_idv)
  | SeqTail ->
      ("Tail",          [ t_cst t_idv ],                      t_idv)
  | SeqSubSeq ->
      ("SubSeq",        [ t_cst t_idv ; t_cst t_idv ; t_cst t_idv ],
                                                              t_idv)
  | SeqSelectSeq ->
      ("SelectSeq",     [ t_cst t_idv ; t_una t_idv t_idv ],  t_idv)
  (* Finite Sets *)
  | FSIsFiniteSet ->
      ("IsFiniteSet",   [ t_cst t_idv ],                      t_bol)
  | FSCard ->
      ("Cardinality",   [ t_cst t_idv ],                      t_idv)

  | _ ->
      error "internal error"
  end

let typed_data tla_smb =
  begin match tla_smb with
  (* Arithmetic *)
  | TIntLit n ->
      ("TIntLit_" ^ string_of_int n,
                        [],                                   t_int,
      IntLit n)
  | TIntPlus ->
      ("TIntPlus",      [ t_cst t_int ; t_cst t_int ],        t_int,
      IntPlus)
  | TIntUminus ->
      ("TIntUminus",    [ t_cst t_int ],                      t_int,
      IntUminus)
  | TIntMinus ->
      ("TIntMinus",     [ t_cst t_int ; t_cst t_int ],        t_int,
      IntMinus)
  | TIntTimes ->
      ("TIntTimes",     [ t_cst t_int ; t_cst t_int ],        t_int,
      IntTimes)
  | TIntQuotient ->
      ("TIntQuotient",  [ t_cst t_int ; t_cst t_int ],        t_int,
      IntQuotient)
  | TIntRemainder ->
      ("TIntRemainder", [ t_cst t_int ; t_cst t_int ],        t_int,
      IntRemainder)
  | TIntExp ->
      ("TIntExp",       [ t_cst t_int ; t_cst t_int ],        t_int,
      IntExp)
  | TIntLteq ->
      ("TIntLteq",      [ t_cst t_int ; t_cst t_int ],        t_bol,
      IntLteq)
  | TIntLt ->
      ("TIntLt",        [ t_cst t_int ; t_cst t_int ],        t_bol,
      IntLt)
  | TIntGteq ->
      ("TIntGteq",      [ t_cst t_int ; t_cst t_int ],        t_bol,
      IntGteq)
  | TIntGt ->
      ("TIntGt",        [ t_cst t_int ; t_cst t_int ],        t_bol,
      IntGt)
  (* Finite Sets *)
  | TFSCard s ->
      ("TFSCard_" ^ ty_to_string s,
                        [ t_cst (t_fs s) ],                   t_int,
      FSCard)
  | TFSMem s ->
      ("TFSMem_" ^ ty_to_string s,
                        [ t_cst s ; t_cst (t_fs s) ],         t_bol,
      Mem)
  | TFSSubseteq s ->
      ("TFSSubseteq_" ^ ty_to_string s,
                        [ t_cst (t_fs s) ; t_cst (t_fs s) ],  t_bol,
      SubsetEq)
  | TFSEmpty s ->
      ("TFSEmpty_" ^ ty_to_string s,
                        [],                                   t_fs s,
      SetEnum 0)
  | TFSSingleton s ->
      ("TFSSingleton_" ^ ty_to_string s,
                        [ t_cst (t_fs s) ],                   t_fs s,
      SetEnum 1)
  | TFSAdd s ->
      ("TFSAdd_" ^ ty_to_string s,
                        [ t_cst s ; t_cst (t_fs s) ],         t_fs s,
      Add)
  | TFSCup s ->
      ("TFSCup_" ^ ty_to_string s,
                        [ t_cst (t_fs s) ; t_cst (t_fs s) ],  t_fs s,
      Cup)
  | TFSCap s ->
      ("TFSCap_" ^ ty_to_string s,
                        [ t_cst (t_fs s) ; t_cst (t_fs s) ],  t_fs s,
      Cap)
  | TFSSetminus s ->
      ("TFSSetminus_" ^ ty_to_string s,
                        [ t_cst (t_fs s) ; t_cst (t_fs s) ],  t_fs s,
      SetMinus)

  | _ ->
      error "internal error"
  end

let special_data tla_smb =
  begin match tla_smb with
  | Cast ty ->
      ("Cast_" ^ ty_to_string ty,
                        [ t_cst ty ],                         t_idv)
  | Proj ty ->
      ("Proj_" ^ ty_to_string ty,
                        [ t_cst t_idv ],                      ty)
  | True ty ->
      ("Tt_" ^ ty_to_string ty,
                        [],                                   ty)
  | Anon (s, Ty2 (ty1s, ty0)) ->
      ("Anon_" ^ s,     ty1s,                                 ty0)
  | ExtTrigEq ty ->
          (* get the sort as it will appear in SMT *)
          let actual_ty =
              match ty with
              | TAtm (TAInt | TABol) -> ty
              | _ -> t_idv
          in
          ("TrigEq_" ^ ty_to_string ty,
                        [ t_cst actual_ty ; t_cst actual_ty ],  t_bol)
  | ExtTrig ->
          ("SetExtTrigger",
                        [ t_cst t_idv ; t_cst t_idv ],        t_bol)
  | IsSetOf ->
          ("IsSetOf",   [ t_cst t_idv ],                      t_bol)

  | _ ->
      error "internal error"
  end

let get_data tla_smb =
  match tla_smb with
  | Choose | Mem | SubsetEq | SetEnum _ | Add | Union | Subset | Cup | Cap
  | SetMinus | SetSt | SetOf _ | BoolSet | StrSet | StrLit _ | IntSet
  | NatSet | IntLit _ | IntPlus | IntUminus | IntMinus | IntTimes
  | IntQuotient | IntRemainder | IntExp | IntLteq | IntLt | IntGteq | IntGt
  | IntRange | FunIsafcn | FunSet | FunConstr | FunDom | FunIm | FunApp
  | FunExcept | Tuple _ | Product _ | Rec _ | RecSet _ | SeqSeq | SeqLen
  | SeqBSeq | SeqCat | SeqAppend | SeqHead | SeqTail | SeqSubSeq
  | SeqSelectSeq | FSIsFiniteSet | FSCard ->
      let (nm, tins, tout) = untyped_data tla_smb in
      { dat_name = "TLA__" ^ nm
      ; dat_ty2  = Ty2 (tins, tout)
      ; dat_kind = Untyped
      ; dat_tver = None
      }
  | TIntLit _ | TIntPlus | TIntUminus | TIntMinus | TIntTimes | TIntQuotient
  | TIntRemainder | TIntExp | TIntLteq | TIntLt | TIntGteq | TIntGt | TFSCard _
  | TFSMem _ | TFSSubseteq _ | TFSEmpty _ | TFSSingleton _ | TFSAdd _ | TFSCup _
  | TFSCap _ | TFSSetminus _ ->
      let (nm, tins, tout, tver) = typed_data tla_smb in
      { dat_name = "TLA__" ^ nm
      ; dat_ty2  = Ty2 (tins, tout)
      ; dat_kind = Typed
      ; dat_tver = Some tver
      }
  | Cast _ | Proj _ | True _ | Anon _ | ExtTrigEq _ | ExtTrig | IsSetOf ->
      let (nm, tins, tout) = special_data tla_smb in
      { dat_name = "TLA__" ^ nm
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

let untyped_deps ~solver tla_smb s =
  let s' =
    match tla_smb with
    | StrLit str ->
        { s with strlits = Ss.add str s.strlits }
    | IntLit n ->
        { s with intlits = Is.add n s.intlits }
    | _ -> s
  in
  let noarith =
    match solver with
    | "Zipper" -> true
    | _ -> Params.debugging "noarith"
  in
  let t0p =
    match noarith with
    | true -> false
    | _ -> Params.debugging "t0+"
  in
  let ext =
    if Params.debugging "noext" then false
    else
      match solver with
      | "SMT" | "Z3" | "CVC4" | "CVC5" | "veriT" -> true
      | _ -> false
  in
  begin match tla_smb with
  (* Logic *)
  | Choose ->
      ([], [ ChooseDef (*; ChooseExt*) ])
  (* Set Theory *)
  | Mem when ext ->
      ([ ExtTrig ],
                  [ SetExt ])
  | Mem ->
      ([],        [ (*SetExt*) ])
  | SubsetEq ->
      ([ Mem ],   [ SubsetEqIntro ; SubsetEqElim ])
  | SetEnum 0 ->
      ([ Mem ],   [ EnumDefElim 0 ])
  | SetEnum n ->
      ([ Mem ],   [ EnumDefIntro n ; EnumDefElim n ])
  | Union ->
      ([ Mem ],   [ UnionIntro ; UnionElim ])
  | Subset ->
      ([ Mem ; SubsetEq ],
                  [ SubsetDefAlt ])
  | Cup ->
      ([ Mem ],   [ CupDef ])
  | Cap when ext ->
          ([ Mem ; SetEnum 0 ; ExtTrig ],
                  [ CapDef ; DisjointTrigger ])
  | Cap ->
      ([ Mem ],   [ CapDef ])
  | SetMinus ->
      ([ Mem ],   [ SetMinusDef ])
  | SetSt when ext ->
      ([ Mem ; SetEnum 0; ExtTrig ],
                  [ SetStDef ; EmptyComprehensionTrigger ])
  | SetSt ->
      ([ Mem ],   [ SetStDef ])
  | SetOf n when ext ->
      ([ Mem ; IsSetOf ],
                  [ SetOfIntro n ; SetOfElim n ; AssertIsSetOf n ; CompareSetOfTrigger ])
  | SetOf n ->
      ([ Mem ],   [ SetOfIntro n ; SetOfElim n ])
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
  | NatSet when noarith ->
      ([ IntSet ; IntLit 0 ; IntLteq ],       [ NatSetDef ])
  | NatSet ->
      ([ IntSet ; TIntLit 0 ; Cast (TAtm TAInt) ; IntLteq ],
                                              [ NatSetDef ])
  | IntLit n ->
      let distincts =
        Is.fold (fun m -> List.cons (IntLitDistinct (m, n))) s.intlits []
      in
      ([ Mem ; IntSet ; IntLit 0 ; IntLteq ] @
        begin if n = 0 && noarith then [ IntLit 1 ] else [] end,
                                              [ IntLitIsint n ; IntLitZeroCmp n ] @ distincts @
                                              begin if n = 0 && noarith then [ NonNegIsPos ] else [] end)
  | IntPlus when noarith ->
      ([ Mem ; IntSet ; NatSet ],             [ IntPlusTyping ; NatPlusTyping ])
  | IntUminus when noarith ->
      ([ Mem ; IntSet ],                      [ IntUminusTyping ])
  | IntMinus when noarith ->
      ([ Mem ; IntSet ],                      [ IntMinusTyping ])
  | IntTimes when noarith ->
      ([ Mem ; IntSet ; NatSet ],             [ IntTimesTyping ; NatTimesTyping ])
  | IntQuotient when noarith ->
      ([ Mem ; IntSet ; NatSet ; IntLteq ; IntLit 0 ],
                                              [ IntQuotientTyping ])
  | IntRemainder when noarith ->
      ([ Mem ; IntSet ; NatSet ; IntLteq ; IntLit 0 ; IntLit 1 ;
          IntRange ; IntMinus ],              [ IntRemainderTyping ])
  | IntExp when noarith ->
      ([ Mem ; IntSet ; IntLit 0 ],           [ IntExpTyping ])
  | IntLteq | IntLt | IntGteq | IntGt when noarith ->
      ([ Mem ; IntSet ],                      [ LteqReflexive ; LteqTransitive ; LteqAntisym ])
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
      ([ Mem ; FunDom ; FunConstr ; FunApp ],
                                  [ FunExt ])
  | FunSet ->
      ([ Mem ; FunIsafcn ; FunDom ; FunApp ],
                                  [ FunSetIntro ; FunSetElim1 ; FunSetElim2 ])
  | FunConstr ->
      ([ FunIsafcn ],             [ FunConstrIsafcn ])
  | FunDom ->
      ([ FunConstr ],             [ FunDomDef ])
  | FunApp ->
      ([ Mem ; FunConstr ],       [ FunAppDef ])
  | FunExcept ->
      ([ Mem ; FunIsafcn ; FunDom ; FunApp ],
                                  [ FunExceptIsafcn ; FunExceptDomDef ; FunExceptAppDef1 ; FunExceptAppDef2 ])
  | FunIm ->
      ([ Mem ; FunDom ; FunApp ], [ FunImIntro ; FunImElim ])
  (* Tuples *)
  | Tuple 0 when noarith ->
      ([ FunIsafcn ; IntLit 0 ; SeqSeq ; SeqLen ],
                                  [ TupIsafcn 0 ; SeqTupTyping 0 ; SeqTupLen 0 ])
  | Tuple 0 ->
      ([ FunIsafcn ; Cast (TAtm TAInt) ; SeqSeq ; SeqLen ],
                                  [ TupIsafcn 0 ; SeqTupTyping 0 ; SeqTupLen 0 ])
  | Tuple n when n > 0 && noarith ->
      (*([ FunIsafcn ; FunDom ; FunApp ; IntRange ]*)
      ([ FunIsafcn ; FunDom ; FunApp ; SetEnum n ; Mem ; SeqSeq ; SeqLen ]
       @ List.init n (fun i -> IntLit (i+1)),
                                  [ TupIsafcn n ; TupDomDef n ; TupAppDef n ; SeqTupTyping n ; SeqTupLen n ])
  | Tuple n when n > 0 && t0p ->
      (*([ FunIsafcn ; FunDom ; FunApp ; TIntRange ],*)
      ([ FunIsafcn ; FunDom ; FunApp ; SetEnum n ; Cast (TAtm TAInt) ; Mem ; SeqSeq ; SeqLen ],
                                  [ TupIsafcn n ; TupDomDef n ; TupAppDef n ; SeqTupTyping n ; SeqTupLen n ])
  | Tuple n when n > 0 ->
      (*([ FunIsafcn ; FunDom ; FunApp ; IntRange ; Cast (TAtm TAInt) ],*)
      ([ FunIsafcn ; FunDom ; FunApp ; SetEnum n ; Cast (TAtm TAInt) ; Mem ; SeqSeq ; SeqLen ],
                                  [ TupIsafcn n ; TupDomDef n ; TupAppDef n ; SeqTupTyping n ; SeqTupLen n ])
  | Product n ->
      ([ Mem ; Tuple n ; FunApp ]
       @ List.init n (fun i ->
         if noarith then IntLit (i + 1)
         else TIntLit (i + 1))
       @ (if noarith then [] else [ Cast (TAtm TAInt) ; Proj (TAtm TAInt) ]),
                                  [ ProductIntro n ; ProductElim n ])
  (* Records *)
  | Rec fs ->
      let n = List.length fs in
      ([ FunIsafcn ; FunDom ; FunApp ; SetEnum n ]
       @ List.map (fun s -> StrLit s) fs,
                                  [ RecIsafcn fs ; RecDomDef fs ; RecAppDef fs ])
  | RecSet fs ->
      ([ Mem ; Rec fs ; FunApp ]
       @ List.map (fun s -> StrLit s) fs,
                                  [ RecSetIntro fs ; RecSetElim fs ])
  (* Sequences *)
  | SeqSeq when noarith ->
      ([ Mem ; SeqLen ; FunIsafcn ; FunDom ; FunApp ; IntSet ; NatSet ; IntRange ; IntLteq ; IntLit 1 ],
                                  [ SeqSetIntro ; SeqSetElim1 ; SeqSetElim2 ])
  | SeqSeq ->
      ([ Mem ; SeqLen ; FunIsafcn ; FunDom ; FunApp ; IntSet ; NatSet ; IntRange ; Cast (TAtm TAInt) ; Proj (TAtm TAInt) ],
                                  [ SeqSetIntro ; SeqSetElim1 ; SeqSetElim2 ])
  | SeqLen when noarith ->
      ([ Mem ; FunDom ; IntRange ; NatSet ; IntLit 1 ],
                                  [ SeqLenDef ])
  | SeqLen ->
      ([ FunDom ; IntRange ; Cast (TAtm TAInt) ],
                                  [ SeqLenDef ])
  | SeqCat when noarith ->
      ([ Mem ; SeqSeq ; SeqLen ; FunApp ; IntSet ; NatSet ; IntPlus ; IntLteq ; IntLit 1 ],
                                  [ SeqCatTyping ; SeqCatLen ; SeqCatApp1 ; SeqCatApp2 ])
  | SeqCat ->
      ([ Mem ; SeqSeq ; SeqLen ; FunApp ; NatSet ; Cast (TAtm TAInt) ; Proj (TAtm TAInt) ],
                                  [ SeqCatTyping ; SeqCatLen ; SeqCatApp1 ; SeqCatApp2 ])
  | SeqAppend when noarith ->
      ([ Mem ; SeqSeq ; SeqLen ; FunApp ; IntSet ; NatSet ; IntPlus ; IntLteq ; IntLit 1 ],
                                  [ SeqAppendTyping ; SeqAppendLen ; SeqAppendApp1 ; SeqAppendApp2 ])
  | SeqAppend ->
      ([ Mem ; SeqSeq ; SeqLen ; FunApp ; NatSet ; Cast (TAtm TAInt) ; Proj (TAtm TAInt) ],
                                  [ SeqAppendTyping ; SeqAppendLen ; SeqAppendApp1 ; SeqAppendApp2 ])
  | SeqHead when noarith ->
      ([ FunApp ; IntLit 1 ],
                                  [ SeqHeadDef ])
  | SeqHead ->
      ([ FunApp ; Cast (TAtm TAInt) ],
                                  [ SeqHeadDef ])
  | SeqTail when noarith ->
      ([ Mem ; SeqSeq ; SeqLen ; FunApp ; IntSet ; NatSet ; IntPlus ; IntMinus ; IntLteq ; IntLit 0 ; IntLit 1 ],
                                  [ SeqTailTyping ; SeqTailLen ; SeqTailApp ])
  | SeqTail ->
      ([ Mem ; SeqSeq ; SeqLen ; FunApp ; NatSet ; Cast (TAtm TAInt) ; Proj (TAtm TAInt) ],
                                  [ SeqTailTyping ; SeqTailLen ; SeqTailApp ])
  | SeqSubSeq when noarith ->
      ([ Mem ; SeqSeq ; SeqLen ; FunApp ; IntSet ; IntPlus ; IntMinus ; IntLteq ; IntLit 0 ; IntLit 1 ],
                                  [ SeqSubseqTyping ; SeqSubseqLen ; SeqSubseqApp ])
  | SeqSubSeq ->
      ([ Mem ; SeqSeq ; SeqLen ; FunApp ; IntSet ; Cast (TAtm TAInt) ; Proj (TAtm TAInt) ],
                                  [ SeqSubseqTyping ; SeqSubseqLen ; SeqSubseqApp ])
  | SeqSelectSeq when noarith ->
      ([ Mem ; SeqSeq ; SeqLen ; SeqAppend ; FunApp ; FunDom ; IntSet ; NatSet ; Tuple 0 ; IntLteq ],
                                  [ SeqSelectseqTyping ; SeqSelectseqLen ; SeqSelectseqNil ; SeqSelectseqApp ; SeqSelectseqAppend ])
  | SeqSelectSeq ->
      ([ Mem ; SeqSeq ; SeqLen ; SeqAppend ; FunApp ; FunDom ; IntSet ; NatSet ; Tuple 0 ; Proj (TAtm TAInt) ],
                                  [ SeqSelectseqTyping ; SeqSelectseqLen ; SeqSelectseqNil ; SeqSelectseqApp ; SeqSelectseqAppend ])
  | SeqBSeq ->
      ([], [])

  | _ ->
      error "internal error"
  end |>
  fun x -> (s', x)

let typed_deps tla_smb s =
  begin match tla_smb with
  (* Arithmetic *)
  | TIntLit _ ->
      ([],                                    [])
  | TIntPlus ->
      ([ IntPlus ],                           [])
  | TIntUminus ->
      ([ IntUminus ],                         [])
  | TIntMinus ->
      ([ IntMinus ],                          [])
  | TIntTimes ->
      ([ IntTimes ],                          [])
  | TIntQuotient ->
      ([ IntQuotient ],                       [])
  | TIntRemainder ->
      ([ IntRemainder ],                      [])
  | TIntExp ->
      ([ IntExp ],                            [])
  (* NOTE Best to declare only Lteq and not the four variants *)
  | TIntLteq ->
      ([ IntLteq ],                           [ Typing TIntLteq ])
  | TIntLt ->
      ([ (*IntLt*) IntLteq ],                 [ Typing TIntLteq ])
  | TIntGteq ->
      ([ (*IntGteq*) IntLteq ],               [ Typing TIntLteq ])
  | TIntGt ->
      ([ (*IntGt*) IntLteq ],                 [ Typing TIntLteq ])
  | _ ->
      error "internal error"
  end |>
  fun x -> (s, x)

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
      (tla_smbs @ (if ty0 = TAtm TABol then [] else [ Proj ty0 ]),
              [ CastInjAlt ty0 ; TypeGuardIntro ty0 ; TypeGuardElim ty0 ])
  | Proj _ ->
      ([], [])
  | True ty0 ->
      ([], [])
  | Anon _ ->
      ([], [])
  | ExtTrigEq (TSet ty01 as ty0) ->
      ([ ExtTrig ],       [ ExtTrigEqDef ty0 ; ExtTrigEqTrigger ty01 ])
  | ExtTrigEq ty0 ->
      ([],                [ ExtTrigEqDef ty0 ])
  | ExtTrig ->
      ([], [])
  | IsSetOf ->
      ([], [])
  | _ ->
      error "internal error"
  end |>
  fun x -> (fun s -> (s, x))

let get_deps ~solver tla_smb s =
  match tla_smb with
  | Choose | Mem | SubsetEq | SetEnum _ | Add | Union | Subset | Cup | Cap
  | SetMinus | SetSt | SetOf _ | BoolSet | StrSet | StrLit _ | IntSet
  | NatSet | IntLit _ | IntPlus | IntUminus | IntMinus | IntTimes
  | IntQuotient | IntRemainder | IntExp | IntLteq | IntLt | IntGteq | IntGt
  | IntRange | FunIsafcn | FunSet | FunConstr | FunDom | FunIm | FunApp
  | FunExcept | Tuple _ | Product _ | Rec _ | RecSet _ | SeqSeq | SeqLen
  | SeqBSeq | SeqCat | SeqAppend | SeqHead | SeqTail | SeqSubSeq
  | SeqSelectSeq | FSIsFiniteSet | FSCard ->
      let s, (smbs, axms) = untyped_deps ~solver tla_smb s in
      s,
      { dat_deps = smbs
      ; dat_axms = axms
      }
  | TIntLit _ | TIntPlus | TIntUminus | TIntMinus | TIntTimes | TIntQuotient
  | TIntRemainder | TIntExp | TIntLteq | TIntLt | TIntGteq | TIntGt
  | TFSCard _ | TFSMem _ | TFSSubseteq _ | TFSEmpty _ | TFSSingleton _
  | TFSAdd _ | TFSCup _ | TFSCap _ | TFSSetminus _ ->

      let s, (smbs, axms) = typed_deps tla_smb s in
      s,
      { dat_deps = smbs
      ; dat_axms = axms
      }
  | Cast _ | Proj _ | True _ | Anon _ | ExtTrigEq _ | ExtTrig | IsSetOf ->
      let s, (smbs, axms) = special_deps tla_smb s in
      s,
      { dat_deps = smbs
      ; dat_axms = axms
      }

