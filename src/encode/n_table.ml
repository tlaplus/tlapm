(*
 * encode/table.ml --- table of symbols used to encode POs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Type.T
open Property

module A = N_axioms


(* {3 Symbols of TLA+} *)

type tla_smb =
  (* Logic *)
  | Choose of ty
  (* Set Theory *)
  | Mem of ty
  | SubsetEq of ty
  | SetEnum of int * ty
  | Union of ty
  | Subset of ty
  | Cup of ty
  | Cap of ty
  | SetMinus of ty
  | SetSt of ty
  | SetOf of ty list * ty
  (* Primitive Sets *)
  | Booleans
  | Strings
  | Ints
  | Nats
  | Reals
  (* Functions *)
  | IsAFcn
  | Arrow of ty * ty
  | Domain of ty * ty
  | FcnApp of ty * ty
  | Fcn of ty * ty
  | Except of ty * ty (* FIXME remove? *)
  (* Arithmetic *)
  | Plus
  | Uminus
  | Minus
  | Times
  | Ratio
  | Quotient
  | Remainder
  | Exp
  | Lteq
  | Range
  | IntLit of int
  (* Strings *)
  | StrLit of string
  (* Special *)
  | Any of ty       (** Random element of a type *)
  | Ucast of ty     (** Cast from any type to uninterpreted *)
  | Uver of tla_smb (** Uninterpreted VERsion of a symbol *)

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

let rec get_tlafam = function
  | Choose _ ->
      Logic
  | Mem _ | SubsetEq _ | SetEnum _ | Union _ | Subset _
  | Cup _ | Cap _ | SetMinus _ | SetSt _ | SetOf _ ->
      Sets
  | Booleans ->
      Booleans
  | Strings | StrLit _ ->
      Strings
  | Ints | Nats | Reals
  | Plus | Uminus | Minus | Times | Ratio | Quotient | Exp | Remainder | Lteq
  | IntLit _ | Range ->
      Arithmetic
  | IsAFcn | Arrow _ | Domain _ | FcnApp _ | Fcn _ | Except _ ->
      Functions
  | Uver smb ->
      get_tlafam smb
  | Any _ | Ucast _ ->
      Special


exception No_value

let smbtable_aux = function
  | Choose ty ->
      [],
      [ A.choose (Some ty) ]
  | SubsetEq ty ->
      [ Mem ty ],
      [ A.subseteq (Some ty) ]
  | SetEnum (n, ty) ->
      [ Mem ty ],
      [ A.setenum n (Some ty) ]
  | Union ty ->
      [ Mem ty ],
      [ A.union (Some ty) ]
  | Subset ty ->
      [ Mem ty ],
      [ A.subset (Some ty) ]
  | Cup ty ->
      [ Mem ty ],
      [ A.cup (Some ty) ]
  | Cap ty ->
      [ Mem ty ],
      [ A.cap (Some ty) ]
  | SetMinus ty ->
      [ Mem ty ],
      [ A.setminus (Some ty) ]
  | SetSt ty ->
      [ Mem ty ],
      [ A.setst (Some ty) ]
  | SetOf (tys, ty) ->
      List.map (fun ty -> Mem ty) tys @
      [ Mem ty ],
      [ A.setof (List.length tys) (Some (tys, ty)) ]
  | Arrow (ty1, ty2) ->
      [ Mem ty1
      ; Mem ty2
      ; Domain (ty1, ty2)
      ; FcnApp (ty1, ty2) ],
      [ A.arrow (Some (ty1, ty2)) ]
  | Fcn (ty1, ty2) ->
      [ Mem ty1
      ; Domain (ty1, ty2)
      ; FcnApp (ty1, ty2) ],
      [ A.domain (Some (ty1, ty2))
      ; A.fcnapp (Some (ty1, ty2)) ]
  | Uver (Choose _) ->
      [ Any (TAtom TU) ],
      [ A.choose None ]
  | Uver (SubsetEq _) ->
      [ Uver (Mem TUnknown) ],
      [ A.subseteq None ]
  | Uver (SetEnum (n, _)) ->
      [ Uver (Mem TUnknown) ],
      [ A.setenum n None ]
  | Uver (Union _) ->
      [ Uver (Mem TUnknown) ],
      [ A.union None ]
  | Uver (Subset _) ->
      [ Uver (Mem TUnknown) ],
      [ A.subset None ]
  | Uver (Cup _) ->
      [ Uver (Mem TUnknown) ],
      [ A.cup None ]
  | Uver (Cap _) ->
      [ Uver (Mem TUnknown) ],
      [ A.cap None ]
  | Uver (SetMinus _) ->
      [ Uver (Mem TUnknown) ],
      [ A.setminus None ]
  | Uver (SetSt _) ->
      [ Any (TAtom TU)
      ; Uver (Mem TUnknown) ],
      [ A.setst None ]
  | Uver (SetOf (tys, _)) ->
      List.map (fun _ -> Uver (Mem TUnknown)) tys @
      [ Any (TAtom TU)
      ; Uver (Mem TUnknown) ],
      [ A.setof (List.length tys) None ]
  | Uver (Arrow _) ->
      [ Uver (Mem TUnknown)
      ; Uver (Domain (TUnknown, TUnknown))
      ; Uver (FcnApp (TUnknown, TUnknown)) ],
      [ A.arrow None ]
  | Uver (Fcn _) ->
      [ Uver (Mem TUnknown)
      (*; IsAFcn*)
      ; Uver (Domain (TUnknown, TUnknown))
      ; Uver (FcnApp (TUnknown, TUnknown)) ],
      [ (*A.fcnisafcn
      ;*) A.domain None
      ; A.fcnapp None ]
  | Uver Plus when !Params.enc_arith ->
      [ Ucast (TAtom TInt)
      ; Plus ],
      [ A.plus_type ]
  | Uver Times when !Params.enc_arith ->
      [ Ucast (TAtom TInt)
      ; Times ],
      [ A.times_type ]
  | Uver Uminus when !Params.enc_arith ->
      [ Ucast (TAtom TInt)
      ; Uminus ],
      [ A.uminus_type ]
  | Uver Minus when !Params.enc_arith ->
      [ Ucast (TAtom TInt)
      ; Minus ],
      [ A.minus_type ]
  | Uver Quotient when !Params.enc_arith ->
      [ Ucast (TAtom TInt)
      ; Quotient ],
      [ A.quotient_type ]
  | Uver Remainder when !Params.enc_arith ->
      [ Ucast (TAtom TInt)
      ; Remainder ],
      [ A.remainder_type ]
  | Uver Exp when !Params.enc_arith ->
      [ Ucast (TAtom TInt)
      ; Exp ],
      [ A.exp_type ]
  | Uver Lteq when !Params.enc_arith ->
      [ Ucast (TAtom TInt)
      ; Lteq ],
      [ A.lteq_type ]
  | Uver Range when !Params.enc_arith ->
      [ Ucast (TAtom TInt)
      ; Range ],
      [ A.range_type ]
  | Any (TAtom TU) ->
      [ Ucast (TAtom TBool) ],
      []
  | Ucast (TAtom TBool) ->
      [ Any (TAtom TU) ],
      [ A.boolcast_inj ]
  | Ucast (TAtom TInt) when !Params.enc_arith ->
      [ Uver Ints
      ; Uver (Mem TUnknown) ],
      [ A.inteq_type
      ; A.int_guard ]
  | _ ->
      raise No_value


(* {3 Symbol Data} *)

type smb =
  { smb_fam  : family
  ; smb_name : string
  ; smb_sch  : ty_sch option (* FIXME remove option *)
  ; smb_kind : ty_kind       (* FIXME remove *)
  ; smb_ord  : int
  ; smb_defn : tla_smb option
  }

let mk_smb fam nm ?sch:sch k =
  let d = ord k in
  if d < 0 || d > 2 then
    let mssg = ("Attempt to create symbol '" ^ nm ^ "' \
                of order " ^ string_of_int d) in
    Errors.bug mssg
  else
    { smb_fam = fam
    ; smb_name = nm
    ; smb_sch = sch
    ; smb_kind = k
    ; smb_ord = ord k
    ; smb_defn = None
    }

let mk_snd_smb fam nm ints outt =
  let ks =
    List.map begin fun (tys, ty) ->
      mk_fstk_ty tys ty
    end ints
  in
  let k = mk_kind_ty ks outt in
  let targs =
    List.map begin function
      | [], ty -> TRg ty
      | tys, ty -> TOp (tys, ty)
    end ints
  in
  let sch = TSch ([], targs, outt) in
  mk_smb fam nm ~sch:sch k

let mk_fst_smb fam nm ints outt =
  let k = mk_fstk_ty ints outt in
  let sch = TSch ([], List.map (fun ty -> TRg ty) ints, outt) in
  mk_smb fam nm ~sch:sch k

let mk_cst_smb fam nm ty =
  let k = mk_cstk_ty ty in
  let sch = TSch ([], [], ty) in
  mk_smb fam nm ~sch:sch k

let get_fam smb = smb.smb_fam
let get_name smb = smb.smb_name
let get_sch smb = Option.get smb.smb_sch
let get_kind smb = smb.smb_kind
let get_ord smb = smb.smb_ord
let get_defn smb = smb.smb_defn

module OrdSmb = struct
  type t = smb
  let compare smb1 smb2 =
    let fam1 = get_fam smb1 in
    let fam2 = get_fam smb2 in
    match Pervasives.compare fam1 fam2 with
    | 0 ->
        let nm1 = get_name smb1 in
        let nm2 = get_name smb2 in
        Pervasives.compare nm1 nm2
    | n -> n
end

let smb_prop = make "Encode.Table.smb_prop"

let has_smb a = has a smb_prop
let set_smb smb a = assign a smb_prop smb
let get_smb a = get a smb_prop


module SmbSet = Set.Make (OrdSmb)
module SmbMap = Map.Make (OrdSmb)


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

let u_ty = function
  | TAtom TBool -> TAtom TBool
  | _ -> TAtom TU

let u_targ = function
  | TRg ty -> TRg (TAtom TU)
  | TOp (tys, ty) -> TOp (List.init (List.length tys) (fun _ -> TAtom TU), u_ty ty)

let u_sch (TSch (vs, targs, ty)) =
  TSch ([], List.map u_targ targs, u_ty ty)

let u_smb smb =
  { smb with
    smb_name = smb.smb_name ^ "___U"
    (*smb_name = smb.smb_name (* NOTE /!\ This works in practise as long as
                             * u_smb is only called on standards symbols
                             * with type argument 'TUnknown' *)*)
  (* FIXME broken for smbs like "+" which cant have argument 'TUnknown' *)
  ; smb_kind = u_kind smb.smb_kind
  ; smb_sch = Option.map u_sch smb.smb_sch
  }


let suffix s ss =
  let ss = List.filter (fun s -> String.length s <> 0) ss in
  String.concat "__" (s :: ss)

let type_to_string ty =
  match ty with
  | TUnknown -> "" (* Empty string will not result in a suffix *)
  | _ -> ty_to_string ty

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

let isafcn =
  let id = "IsAFcn" in
  mk_fst_smb Functions id [ TAtom TU ; TAtom TU ] (TAtom TBool)
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

let uminus =
  let id = "Uminus" in
  mk_fst_smb Arithmetic id [ TAtom TInt ] (TAtom TInt)
let plus =
  let id = "Plus" in
  mk_fst_smb Arithmetic id [ TAtom TInt ; TAtom TInt ] (TAtom TInt)
let minus =
  let id = "Minus" in
  mk_fst_smb Arithmetic id [ TAtom TInt ; TAtom TInt ] (TAtom TInt)
let times =
  let id = "Times" in
  mk_fst_smb Arithmetic id [ TAtom TInt ; TAtom TInt ] (TAtom TInt)
let ratio =
  let id = "Ratio" in
  mk_fst_smb Arithmetic id [ TAtom TInt ; TAtom TInt ] (TAtom TInt)
let quotient =
  let id = "Quotient" in
  mk_fst_smb Arithmetic id [ TAtom TInt ; TAtom TInt ] (TAtom TInt)
let remainder =
  let id = "Remainder" in
  mk_fst_smb Arithmetic id [ TAtom TInt ; TAtom TInt ] (TAtom TInt)
let exp =
  let id = "Exp" in
  mk_fst_smb Arithmetic id [ TAtom TInt ; TAtom TInt ] (TAtom TInt)
let lteq =
  let id = "Lteq" in
  mk_fst_smb Arithmetic id [ TAtom TInt ; TAtom TInt ] (TAtom TBool)
let range =
  let id = "Range" in
  mk_fst_smb Arithmetic id [ TAtom TInt ; TAtom TInt ] (TSet (TAtom TInt))
let intlit n =
  let id = "IntLit_" ^ string_of_int n in
  mk_cst_smb Arithmetic id (TAtom TInt)

let product tys =
  let id = suffix "Product" (List.map type_to_string tys) in
  mk_fst_smb Tuples id tys (TSet (TProd tys))
let tuple tys =
  let id = suffix "Tuple" (List.map type_to_string tys) in
  mk_fst_smb Tuples id tys (TProd tys)

let strlit s =
  let id = "StrLit_" ^ s in
  mk_cst_smb Strings id (TAtom TStr)

let any ty =
  let id = suffix "tt" [ type_to_string ty ] in
  mk_cst_smb Special id ty

let ucast ty =
  let id = suffix "Cast" [ type_to_string ty ] in
  mk_fst_smb Special id [ ty ] (TAtom TU)


let rec std_smb_aux = function
  | Choose ty -> choose ty
  | Mem ty -> mem ty
  | SubsetEq ty -> subseteq ty
  | SetEnum (n, ty) -> setenum n ty
  | Union ty -> union ty
  | Subset ty -> subset ty
  | Cup ty -> cup ty
  | Cap ty -> cap ty
  | SetMinus ty -> setminus ty
  | SetSt ty -> setst ty
  | SetOf (tys, ty) -> setof tys ty
  | Booleans -> set_boolean
  | Strings -> set_string
  | Ints -> set_int
  | Nats -> set_nat
  | Reals -> set_real
  | IsAFcn -> isafcn
  | Arrow (ty1, ty2) -> arrow ty1 ty2
  | Domain (ty1, ty2) -> domain ty1 ty2
  | FcnApp (ty1, ty2) -> fcnapp ty1 ty2
  | Fcn (ty1, ty2) -> fcn ty1 ty2
  | Except (ty1, ty2) -> except ty1 ty2
  | Uminus -> uminus
  | Plus -> plus
  | Minus -> minus
  | Times -> times
  | Ratio -> ratio
  | Quotient -> quotient
  | Remainder -> remainder
  | Exp -> exp
  | Range -> range
  | Lteq -> lteq
  | IntLit n -> intlit n
  | StrLit s -> strlit s
  | Any ty -> any ty
  | Ucast ty -> ucast ty
  | Uver tla_smb -> u_smb (std_smb_aux tla_smb)


let std_smb tla_smb =
  { (std_smb_aux tla_smb) with smb_defn = Some tla_smb }


let detect = function
  | "IsAFcn" -> Some IsAFcn
  | "tt" -> Some (Any (TAtom TU))
  | "Cast_Bool" -> Some (Ucast (TAtom TBool))
  | "Cast_SetBool" -> Some (Ucast (TSet (TAtom TBool)))
  | "Cast_Int" -> Some (Ucast (TAtom TInt))
  | "Cast_SetInt" -> Some (Ucast (TSet (TAtom TInt)))
  | "Plus_Int" -> Some Plus
  | "Times_Int" -> Some Times
  | "Uminus_Int" -> Some Uminus
  | "Minus_Int" -> Some Minus
  | "Quotient_Int" -> Some Quotient
  | "Remainder_Int" -> Some Remainder
  | "Exp_Int" -> Some Exp
  | "Lteq_Int" -> Some Lteq
  | "Range_Int" -> Some Range
  | _ -> None

let decode_visitor = object (self : 'self)
  inherit [unit] Expr.Visit.map as super
  method expr scx oe =
    let oe =
      Option.fold begin fun oe pats ->
        let pats =
          List.map begin fun pat ->
            List.map begin fun e ->
              self#expr scx e
            end pat
          end pats
        in
        assign oe Expr.T.pattern_prop pats
      end oe (query oe Expr.T.pattern_prop)
    in
    match oe.core with
    | Opaque s when has oe A.special_prop ->
        Option.fold begin fun _ tla_smb ->
          let smb = std_smb tla_smb in
          let e = Expr.T.Opaque (get_name smb) %% [] in
          assign e smb_prop smb
        end oe (detect s)
    | _ -> super#expr scx oe
end

let decode e =
  let scx = ((), Deque.empty) in
  decode_visitor#expr scx e

let smbtable smb =
  try
    let smbs, axms = smbtable_aux smb in
    let axms = List.map decode axms in
    Some (smbs, axms)
  with No_value -> None

