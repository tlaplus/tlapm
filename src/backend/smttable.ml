(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

open Format

open Ext
open Expr.T
open Type.T
open Fmtutil
open Property

open Util.Coll

module B = Builtin

(* {3 Generic SMT Declarations} *)

type fmt = Format.formatter -> unit -> unit

type smb =
  | Srt of int
  | Fun of ty list * ty
  | Axm of fmt

type decl =
  { id : string
  ; content : smb
  ; hidden : bool
  }

let mk_sdecl ?(hidden=false) id ar =
  { id = id
  ; content = Srt ar
  ; hidden = hidden
  }

let mk_fdecl ?(hidden=false) id isig osig =
  { id = id
  ; content = Fun (isig, osig)
  ; hidden = hidden
  }

let mk_adecl ?(hidden=false) id ff =
  { id = id
  ; content = Axm ff
  ; hidden = hidden
  }

let pp_print_tyatom ff = function
  | TBool -> pp_print_string ff "Bool"
  | TAtSet -> pp_print_string ff "set"
  | TInt -> pp_print_string ff "Int"
  | TReal -> pp_print_string ff "real"
  | TStr -> pp_print_string ff "str"

let pp_print_srt ff = function
  | TVar v -> pp_print_string ff v
  | TAtom a -> pp_print_tyatom ff a
  | TUnknown -> pp_print_string ff "?"
  | _ -> invalid_arg "Backend.SmtTable.pp_print_srt: not a valid type"

let pp_print_decl ff d =
  if d.hidden then
    fprintf ff "@[; omitted %s: %s@]"
    (match d.content with
    | Srt _ -> "sort declaration"
    | Fun _ -> "function declaration"
    | Axm _ -> "axiom")
    d.id
  else begin
    match d.content with
    | Srt ar ->
        fprintf ff "@[(declare-sort %s %d@])" d.id ar
    | Fun (isig, osig) ->
        fprintf ff "@[(declare-fun %s @[(%a@]) %a@])" d.id
        (pp_print_delimited ~sep:(fun ff () -> pp_print_string ff " ") pp_print_srt)
        isig pp_print_srt osig
    | Axm fmt ->
        fprintf ff "@[(assert %a@])" fmt ()
  end


(* {3 Abstract Symbols} *)

module type Collector = sig
  type smb
  val get_id : smb -> string
  val get_decl : smb -> decl
  val collect : sequent -> smb Sm.t
end

module type Deps = sig
  module C : Collector
  val deps : C.smb -> C.smb Sm.t
end

module Make (D : Deps) = struct
  include D.C

  let choose_opt m =
    try Some (Sm.choose m)
    with Not_found -> None

  let union f m1 m2 =
    Sm.merge begin fun k a b -> match a, b with
      | None, None -> None
      | Some v, None | None, Some v -> Some v
      | Some v1, Some v2 -> Some (f k v1 v2)
    end m1 m2

  (* The heart of this module is this function;
   * dependencies are followed in an exhaustive way,
   * no node is treated twice. *)
  let collect sq =
    let rec more acc untreated =
      match choose_opt untreated with
      | None -> acc
      | Some (id, smb) when Sm.mem id acc ->
          (* prevent circularity *)
          let untreated = Sm.remove id untreated in
          more acc untreated
      | Some (id, smb) ->
          let deps = D.deps smb in
          let acc = Sm.add id smb acc in
          let untreated = Sm.remove id untreated in
          let untreated = union (fun _ _ _ -> assert false) deps untreated in
          more acc untreated
    in
    more Sm.empty (D.C.collect sq)
end


(* {3 Concrete Tables} *)

(* {4 No Types Encoding} *)

(* FIXME remove Bool and Int since they need not be declared? *)
type nt_srt_t =
  | NT_Set
  | NT_Bool
  | NT_Int
  | NT_Real
  | NT_Str

type nt_fun_t =
  | NT_TLA_STRING
  | NT_TLA_BOOLEAN
  | NT_TLA_SUBSET
  | NT_TLA_UNION
  | NT_TLA_DOMAIN
  | NT_TLA_subseteq
  | NT_TLA_in
  | NT_TLA_setminus
  | NT_TLA_cap
  | NT_TLA_cup
  | NT_TLA_Enum of int
  | NT_TLA_Prod of int
  | NT_TLA_tuple of int
  | NT_TLA_fcnapp
  | NT_TLA_Arrow
  | NT_TLA_Rect of int
  | NT_TLA_record of int
  | NT_TLA_except
  | NT_Arith_N
  | NT_Arith_Z
  | NT_Arith_R
  | NT_Arith_plus
  | NT_Arith_uminus
  | NT_Arith_minus
  | NT_Arith_ratio
  | NT_Arith_quotient
  | NT_Arith_remainder
  | NT_Arith_exp
  | NT_Arith_intexp
  | NT_Arith_Infinity
  | NT_Arith_range
  | NT_Arith_intrange
  | NT_Arith_lteq
  | NT_Arith_lt
  | NT_Arith_gteq
  | NT_Arith_gt
  | NT_Cast_BoolToSet
  | NT_Cast_IntToSet
  | NT_Cast_IntToReal
  | NT_Cast_RealToSet
  | NT_Cast_StrToSet

type nt_axm_t =
  | NT_SetExt
  | NT_SubseteqDef
  | NT_EmptyDef
  | NT_EnumDef of int
  (* TODO all axioms *)

type nt_smb =
  | NT_Srt of nt_srt_t
  | NT_Fun of nt_fun_t
  | NT_Axm of nt_axm_t

module NT_Basic_Collector = struct
  type smb = nt_smb

  let tla_prefix = "TLA__"
  let arith_prefix = "arith__"

  let get_sid = function
    | NT_Set -> "set"
    | NT_Bool -> "Bool"
    | NT_Int -> "Int"
    | NT_Real -> "real"
    | NT_Str -> "str"
  let get_fid = function
    | NT_TLA_STRING -> tla_prefix ^ "STRING"
    | NT_TLA_BOOLEAN -> tla_prefix ^ "BOOLEAN"
    | NT_TLA_SUBSET -> tla_prefix ^ "SUBSET"
    | NT_TLA_UNION -> tla_prefix ^ "UNION"
    | NT_TLA_DOMAIN -> tla_prefix ^ "DOMAIN"
    | NT_TLA_subseteq -> tla_prefix ^ "subseteq"
    | NT_TLA_in -> tla_prefix ^ "in"
    | NT_TLA_setminus -> tla_prefix ^ "setminus"
    | NT_TLA_cap -> tla_prefix ^ "cap"
    | NT_TLA_cup -> tla_prefix ^ "cup"
    | NT_TLA_Enum n ->
        if n = 0 then tla_prefix ^ "Empty"
        else tla_prefix ^ "Enum_" ^ string_of_int n
    | NT_TLA_Prod n ->
        if n = 0 then tla_prefix ^ "Unit"
        else if n = 1 then invalid_arg (tla_prefix ^ "Prod_1")
        else tla_prefix ^ "Prod_" ^ string_of_int n
    | NT_TLA_tuple n ->
        if n = 0 then tla_prefix ^ "unit"
        else if n = 1 then invalid_arg (tla_prefix ^ "tuple_1")
        else tla_prefix ^ "tuple_" ^ string_of_int n
    | NT_TLA_fcnapp -> tla_prefix ^ "fcnapp"
    | NT_TLA_Arrow -> tla_prefix ^ "Arrow"
    | NT_TLA_Rect n -> tla_prefix ^ "Rect" ^ string_of_int n
    | NT_TLA_record n -> tla_prefix ^ "record" ^ string_of_int n
    | NT_TLA_except -> tla_prefix ^ "except"
    | NT_Arith_N -> arith_prefix ^ "N"
    | NT_Arith_Z -> arith_prefix ^ "Z"
    | NT_Arith_R -> arith_prefix ^ "R"
    | NT_Arith_plus -> arith_prefix ^ "plus"
    | NT_Arith_uminus -> arith_prefix ^ "uminus"
    | NT_Arith_minus -> arith_prefix ^ "minus"
    | NT_Arith_ratio -> arith_prefix ^ "ratio"
    | NT_Arith_quotient -> arith_prefix ^ "quotient"
    | NT_Arith_remainder -> arith_prefix ^ "remainder"
    | NT_Arith_exp -> arith_prefix ^ "exp"
    | NT_Arith_intexp -> arith_prefix ^ "intexp"
    | NT_Arith_Infinity -> arith_prefix ^ "Infinity"
    | NT_Arith_range -> arith_prefix ^ "range"
    | NT_Arith_intrange -> arith_prefix ^ "intrange"
    | NT_Arith_lteq -> arith_prefix ^ "lteq"
    | NT_Arith_lt -> arith_prefix ^ "lt"
    | NT_Arith_gteq -> arith_prefix ^ "gteq"
    | NT_Arith_gt -> arith_prefix ^ "gt"
    | NT_Cast_BoolToSet -> "BoolToSet"
    | NT_Cast_IntToSet -> "IntToSet"
    | NT_Cast_IntToReal -> "IntToReal"
    | NT_Cast_RealToSet -> "RealToSet"
    | NT_Cast_StrToSet -> "StrToSet"
  let get_aid = function
    | NT_SetExt -> "set extensionality"
    | NT_SubseteqDef -> "subseteq definition"
    | NT_EmptyDef -> "empty set definition"
    | NT_EnumDef n -> "enum " ^ string_of_int n ^ " set definition"
  let get_id = function
    | NT_Srt smb -> get_sid smb
    | NT_Fun smb -> get_fid smb
    | NT_Axm smb -> get_aid smb

  let get_sdecl smb =
    let id = get_sid smb in
    match smb with
    | NT_Set -> mk_sdecl id 0
    | NT_Bool -> mk_sdecl ~hidden:true id 0
    | NT_Int -> mk_sdecl ~hidden:true id 0
    | NT_Real-> mk_sdecl id 0
    | NT_Str -> mk_sdecl id 0
  let get_fdecl smb =
    let id = get_fid smb in
    let isig, osig =
      match smb with
      | NT_TLA_STRING -> [], ty_aset
      | NT_TLA_BOOLEAN -> [], ty_aset
      | NT_TLA_SUBSET -> [ty_aset], ty_aset
      | NT_TLA_UNION -> [ty_aset], ty_aset
      | NT_TLA_DOMAIN -> [ty_aset], ty_aset
      | NT_TLA_subseteq -> [ty_aset; ty_aset], ty_bool
      | NT_TLA_in -> [ty_aset; ty_aset], ty_bool
      | NT_TLA_setminus -> [ty_aset; ty_aset], ty_aset
      | NT_TLA_cap -> [ty_aset; ty_aset], ty_aset
      | NT_TLA_cup -> [ty_aset; ty_aset], ty_aset
      | NT_TLA_Enum n -> (List.init n (fun _ -> ty_aset)), ty_aset
      | NT_TLA_Prod n ->
          if n = 0 then [], ty_aset
          else if n = 1 then invalid_arg "cannot define 'TLA__Prod_1'"
          else (List.init n (fun _ -> ty_aset)), ty_aset
      | NT_TLA_tuple n ->
          if n = 0 then [], ty_aset
          else if n = 1 then invalid_arg "cannot define 'TLA__tuple_1'"
          else (List.init n (fun _ -> ty_aset)), ty_aset
      | NT_TLA_fcnapp -> [ty_aset; ty_aset], ty_aset
      | NT_TLA_Arrow -> [ty_aset; ty_aset], ty_aset
      | NT_TLA_Rect n -> (List.init (2*n) (fun _ -> ty_aset)), ty_aset
      | NT_TLA_record n -> (List.init (2*n) (fun _ -> ty_aset)), ty_aset
      | NT_TLA_except -> [ty_aset; ty_aset; ty_aset], ty_aset
      | NT_Arith_N -> [], ty_aset
      | NT_Arith_Z -> [], ty_aset
      | NT_Arith_R -> [], ty_aset
      | NT_Arith_plus -> [ty_aset; ty_aset], ty_aset
      | NT_Arith_uminus -> [ty_aset], ty_aset
      | NT_Arith_minus -> [ty_aset; ty_aset], ty_aset
      | NT_Arith_ratio -> [ty_aset; ty_aset], ty_aset
      | NT_Arith_quotient -> [ty_aset; ty_aset], ty_aset
      | NT_Arith_remainder -> [ty_aset; ty_aset], ty_aset
      | NT_Arith_exp -> [ty_aset; ty_aset], ty_aset
      | NT_Arith_intexp -> [ty_int; ty_int], ty_aset
      | NT_Arith_Infinity -> [], ty_real
      | NT_Arith_range -> [ty_aset; ty_aset], ty_aset
      | NT_Arith_intrange -> [ty_int; ty_int], ty_aset
      | NT_Arith_lteq -> [ty_aset; ty_aset], ty_bool
      | NT_Arith_lt -> [ty_aset; ty_aset], ty_bool
      | NT_Arith_gteq -> [ty_aset; ty_aset], ty_bool
      | NT_Arith_gt -> [ty_aset; ty_aset], ty_bool
      | NT_Cast_BoolToSet -> [ty_bool], ty_aset
      | NT_Cast_IntToSet -> [ty_int], ty_aset
      | NT_Cast_IntToReal -> [ty_int], ty_real
      | NT_Cast_RealToSet -> [ty_real], ty_aset
      | NT_Cast_StrToSet -> [ty_str], ty_aset
    in mk_fdecl id isig osig
  let get_adecl axm =
    let id = get_aid axm in
    let fmt = fun ff () ->
      match axm with
      | NT_SetExt ->
          fprintf ff "@[<hov 2>(forall ((x set) (y set)) @[<hov 2>(@,\
                        => @[<hov 2>(@,forall ((z set)) @[<hov 2>(@,\
                              (= (TLA__in z x) (TLA__in z y))@]@,)@]@,)\
                          (= x y)@]@,)@]@,)"
      | NT_SubseteqDef ->
          fprintf ff "@[<hov 2>(forall ((x set) (y set)) @[<hov 2>(@,\
                        = @[<hov 2>(@,TLA__subseteq x y@]@,) \
                          @[<hov 2>(@,forall ((z set)) @[<hov 2>(@,\
                            => (TLA__in z x) (TLA__in z y)@]@,)@]@,)\
                      @]@,)@]@]@,)"
      | NT_EmptyDef ->
          fprintf ff "@[<hov 2>(forall ((x set)) @[<hov 2>(@,\
                        not @[<hov 2>(@,TLA__in x TLA__Empty@]@,)\
                      @]@,)@]@,)"
      | NT_EnumDef n ->
          let pars = List.init n (fun i -> "a" ^ string_of_int (i+1)) in
          let bs = List.map (fun a -> "(" ^ a ^ " set)") pars |> String.concat " " in
          let vec = String.concat " " pars in
          fprintf ff "@[<hov 2>(forall @[<hov 2>(@,%s (x set)@]@,) @[<hov 2>(@,\
                        = @[<hov 2>(@,TLA__in x @[<hov 2>(@,TLA__Enum_%d %s@]@,)@]@,)\
                          @[<hov 2>(@,or %a@]@,)\
                      @]@,)@]@,)"
            bs n vec
            (pp_print_delimited ~sep:pp_print_space begin fun ff a ->
              fprintf ff "@[<hov 2>(@,TLA__in x %s@]@,)" a
            end) pars
    in mk_adecl id fmt
  let get_decl = function
    | NT_Srt smb -> get_sdecl smb
    | NT_Fun smb -> get_fdecl smb
    | NT_Axm smb -> get_adecl smb

  let add smb col =
    Sm.add (get_id smb) smb col

  let visitor = object (self : 'self)
    inherit [unit, smb Sm.t] Expr.Visit.fold as super

    method expr scx col oe =
      let l =
        match oe.core with
        | Opaque "BoolToSet" ->
            [ NT_Fun NT_Cast_BoolToSet ]
        | Opaque "IntToSet" ->
            [ NT_Fun NT_Cast_IntToSet ]
        | Opaque "IntToReal" ->
            [ NT_Fun NT_Cast_IntToReal ]
        | Opaque "RealToSet" ->
            [ NT_Fun NT_Cast_RealToSet ]
        | Opaque "StrToSet" ->
            [ NT_Fun NT_Cast_StrToSet ]
        | Opaque "arith__plus" ->
            [ NT_Fun NT_Arith_plus ]
        | Opaque "arith__uminus" ->
            [ NT_Fun NT_Arith_uminus ]
        | Opaque "arith__minus" ->
            [ NT_Fun NT_Arith_minus ]
        | Opaque "arith__ratio" ->
            [ NT_Fun NT_Arith_ratio ]
        | Opaque "arith__quotient" ->
            [ NT_Fun NT_Arith_quotient ]
        | Opaque "arith__remainder" ->
            [ NT_Fun NT_Arith_remainder ]
        | Opaque "arith__exp" ->
            [ NT_Fun NT_Arith_exp ]
        | Opaque "arith__range" ->
            [ NT_Fun NT_Arith_range ]
        | Internal B.STRING ->
            [ NT_Fun NT_TLA_STRING ]
        | Internal B.BOOLEAN ->
            [ NT_Fun NT_TLA_BOOLEAN ]
        | Internal B.SUBSET ->
            [ NT_Fun NT_TLA_SUBSET ]
        | Internal B.UNION ->
            [ NT_Fun NT_TLA_UNION ]
        | Internal B.DOMAIN ->
            [ NT_Fun NT_TLA_DOMAIN ]
        | Internal B.Subseteq ->
            [ NT_Fun NT_TLA_subseteq ]
        | Internal B.Mem | Internal B.Notmem ->
            [ NT_Fun NT_TLA_in ]
        | Internal B.Setminus ->
            [ NT_Fun NT_TLA_setminus ]
        | Internal B.Cap ->
            [ NT_Fun NT_TLA_cap ]
        | Internal B.Cup ->
            [ NT_Fun NT_TLA_cup ]
        | Internal B.Nat ->
            [ NT_Fun NT_Arith_N ]
        | Internal B.Int ->
            [ NT_Fun NT_Arith_Z ]
        | Internal B.Real ->
            [ NT_Fun NT_Arith_R ]
        | Internal B.Exp ->
            [ NT_Fun NT_Arith_intexp ]
        | Internal B.Infinity ->
            [ NT_Fun NT_Arith_Infinity ]
        | Internal B.Range ->
            [ NT_Fun NT_Arith_intrange ]
        | SetEnum es ->
            let n = List.length es in
            [ NT_Fun (NT_TLA_Enum n) ]
        | Product es ->
            let n = List.length es in
            [ NT_Fun (NT_TLA_Prod n) ]
        | Tuple es ->
            let n = List.length es in
            [ NT_Fun (NT_TLA_tuple n) ]
        | FcnApp _ ->
            [ NT_Fun NT_TLA_fcnapp ]
        | Arrow _ ->
            [ NT_Fun NT_TLA_Arrow ]
        | Rect fs ->
            let n = List.length fs in
            [ NT_Fun (NT_TLA_Rect n) ]
        | Record fs ->
            let n = List.length fs in
            [ NT_Fun (NT_TLA_record n) ]
        | Except _ ->
            [ NT_Fun NT_TLA_except ]
        (* TODO finish collect function *)
        | _ -> []
      in
      let col = List.fold_right add l col in
      super#expr scx col oe
  end

  let collect sq =
    let scx = ((), Deque.empty) in
    let init_col =
      List.fold_left begin fun col smb ->
        add smb col
      end Sm.empty begin
        [
          (* Very common symbols; always declared *)
          NT_Srt NT_Set
        ; NT_Fun NT_TLA_in
        ; NT_Fun (NT_TLA_Enum 0)
        ] end
    in
    snd (visitor#sequent scx init_col sq)
end

module NT_Deps = struct
  module C = NT_Basic_Collector

  let deps smb =
    let l = match smb with
    | NT_Fun NT_TLA_subseteq -> [NT_Axm NT_SubseteqDef]
    | NT_Fun (NT_TLA_Enum 0) -> [NT_Axm NT_EmptyDef]
    | NT_Fun (NT_TLA_Enum n) -> [NT_Axm (NT_EnumDef n)]
    | NT_Fun NT_Cast_StrToSet -> [NT_Srt NT_Str]
    (* TODO all dependencies *)
    | _ -> []
    in
    List.fold_left begin fun deps smb ->
      let id = C.get_id smb in
      Sm.add id smb deps
    end Sm.empty l
end

module NT_Collector = Make (NT_Deps)

