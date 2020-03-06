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

module B = Builtin


(* {3 Helpers} *)

let nt_prefix = "NT__"

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

let mk_fact e =
  Fact (e, Visible, Now)

let app b es = Apply (Internal b %% [], es)

let una b e1    = app b [ e1 ]
let ifx b e1 e2 = app b [ e1 ; e2 ]

let quant q xs ?ss e =
  match ss with
  | None ->
      Quant (q, List.map (fun x ->
        (annot_sort (x %% []) TU, Constant, No_domain)
      ) xs, e)
  | Some ss ->
      let xs = List.map2 (fun x s ->
        (annot_sort (x %% []) s, Constant, No_domain)
      ) xs ss in
      Quant (q, xs, e)

let all xs ?ss e = quant Forall xs ?ss e
let exi xs ?ss e = quant Exists xs ?ss e

let gen x n = List.init n (fun i -> x ^ string_of_int (i + 1))
(** [gen "x" n] = [ "x1" ; .. ; "xn" ] *)

let ixi ?(shift=0) n = List.init n (fun i -> Ix (shift + n - i) %% [])
(** [ixi n]          = [ Ix n ; .. ; Ix 2 ; Ix 1 ]
    [ixi ~shift:s n] = [ Ix (s+n) ; .. ; Ix (s+2) ; Ix (s+1) ]
*)


(* {3 Logic} *)

let choose_nm s _ = nt_prefix ^ "Choose_" ^ s

let choose_decl s k =
  let ins =
    match k with
    | TKind (ks, TAtom TU) ->
        List.map (fun k -> get_atom (get_ty k)) ks
    | _ -> invalid_arg ("Reduce.NtAxioms.choose_decl: \
                        bad kind provided")
  in
  mk_fresh (choose_nm s k) ins TU %% []

let critical_def s (TKind (ks, _) as k) body =
  let ss = List.map (fun k -> get_atom (get_ty k)) ks in
  let n = List.length ss in
  all (gen "a" n @ [ "x" ]) ~ss:(ss @ [ TU ]) (
    ifx B.Implies (
      body (* Dark magic *)
    ) (
      let c =
        Apply (Opaque (choose_nm s k) %% [], ixi ~shift:1 n) %% []
      in
      let sub = Expr.Subst.scons c (Expr.Subst.shift 1) in
      Expr.Subst.app_expr sub body
    ) %% []
  ) %% []

let critical_fact s k e = mk_fact (critical_def s k e) %% []


(* {3 Set Theory} *)

let usort_nm = nt_prefix ^ "U"
let uany_nm = nt_prefix ^ "any_u"

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
let setof_nm s _ _ = nt_prefix ^ "SetOf_" ^ s

let uany_decl = mk_fresh uany_nm [] TU %% []

let mem_decl = mk_fresh mem_nm [ TU ; TU ] TBool %% []
let subseteq_decl = mk_fresh subseteq_nm [ TU ; TU ] TBool %% []
let empty_decl = mk_fresh empty_nm [] TU %% []
let enum_decl n = mk_fresh (enum_nm n) (List.init n (fun _ -> TU)) TU %% []
let union_decl = mk_fresh union_nm [ TU ] TU %% []
let power_decl = mk_fresh power_nm [ TU ] TU %% []
let cup_decl = mk_fresh cup_nm [ TU ; TU ] TU %% []
let cap_decl = mk_fresh cap_nm [ TU ; TU ] TU %% []
let setminus_decl = mk_fresh setminus_nm [ TU ; TU ] TU %% []

let setst_decl s k =
  let ins =
    match k with
    | TKind (TKind ([], TAtom TU) :: ks, TAtom TU) ->
        List.map (fun k -> get_atom (get_ty k)) ks
    | _ -> invalid_arg ("Reduce.NtAxioms.setst_decl: \
                        bad kind provided")
  in
  mk_fresh (setst_nm s k) (TU :: ins) TU %% []

let setof_decl s n k =
  let ins =
    match k with
    | TKind (ks, TAtom TU) ->
        let rec spin n ks =
          if n = 0 then ks
          else
            match ks with
            | TKind ([], TAtom TU) :: ks ->
                spin (n - 1) ks
            | _ -> invalid_arg ("Reduce.NtAxioms.setof_decl: \
                                  bad kind provided")
        in
        List.map (fun k -> get_atom (get_ty k)) (spin n ks)
    | _ -> invalid_arg ("Reduce.NtAxioms.setof_decl: \
                        bad kind provided")
  in
  mk_fresh (setof_nm s n k) (List.init n (fun _ -> TU) @ ins) TU %% []

let subseteq_def =
  all [ "x" ; "y" ] (
    ifx B.Equiv (
      ifx B.Subseteq (Ix 2 %% []) (Ix 1 %% []) %% []
    ) (
      all [ "z" ] (
        ifx B.Implies (
          ifx B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
        ) (
          ifx B.Mem (Ix 1 %% []) (Ix 2 %% []) %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

let empty_def =
  all [ "x" ] (
    una B.Neg (
      ifx B.Mem (Ix 1 %% []) (SetEnum [] %% []) %% []
    ) %% []
  ) %% []

let enum_def n =
  if n = 0 then
    empty_def
  else
    all (gen "a" n @ [ "x" ]) (
      ifx B.Equiv (
        ifx B.Mem (
          Ix 1 %% []
        ) (
          SetEnum (ixi ~shift:1 n) %% []
        ) %% []
      ) (
        List (Or, List.init n begin fun i ->
          ifx B.Eq (Ix 1 %% []) (Ix (n - i + 1) %% []) %% []
        end) %% []
      ) %% []
    ) %% []

let union_def =
  all [ "a" ; "x" ] (
    ifx B.Equiv (
      ifx B.Mem (Ix 1 %% []) (una B.UNION (Ix 2 %% []) %% []) %% []
    ) (
      exi [ "y" ] (
        ifx B.Conj (
          ifx B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
        ) (
          ifx B.Mem (Ix 2 %% []) (Ix 1 %% []) %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

let power_def =
  all [ "a" ; "x" ] (
    ifx B.Equiv (
      ifx B.Mem (Ix 1 %% []) (una B.SUBSET (Ix 2 %% []) %% []) %% []
    ) (
      all [ "y" ] (
        ifx B.Implies (
          ifx B.Mem (Ix 1 %% []) (Ix 2 %% []) %% []
        ) (
          ifx B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

let cup_def =
  all [ "a" ; "b" ; "x" ] (
    ifx B.Equiv (
      ifx B.Mem (
        Ix 1 %% []
      ) (
        ifx B.Cup (Ix 3 %% []) (Ix 2 %% []) %% []
      ) %% []
    ) (
      ifx B.Disj (
        ifx B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
      ) (
        ifx B.Mem (Ix 1 %% []) (Ix 2 %% []) %% []
      ) %% []
    ) %% []
  ) %% []

let cap_def =
  all [ "a" ; "b" ; "x" ] (
    ifx B.Equiv (
      ifx B.Mem (
        Ix 1 %% []
      ) (
        ifx B.Cap (Ix 3 %% []) (Ix 2 %% []) %% []
      ) %% []
    ) (
      ifx B.Conj (
        ifx B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
      ) (
        ifx B.Mem (Ix 1 %% []) (Ix 2 %% []) %% []
      ) %% []
    ) %% []
  ) %% []

let setminus_def =
  all [ "a" ; "b" ; "x" ] (
    ifx B.Equiv (
      ifx B.Mem (
        Ix 1 %% []
      ) (
        ifx B.Setminus (Ix 3 %% []) (Ix 2 %% []) %% []
      ) %% []
    ) (
      ifx B.Conj (
        ifx B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
      ) (
        una B.Neg (
          ifx B.Mem (Ix 1 %% []) (Ix 2 %% []) %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

let setst_def s (TKind (ks, _) as k) body =
  let ss = List.map (fun k -> get_atom (get_ty k)) ks in
  let ss = List.tl ss in
  let n = List.length ss in
  all ([ "s" ] @ gen "a" n @ [ "x" ]) ~ss:([ TU ] @ ss @ [ TU ]) (
    ifx B.Equiv (
      ifx B.Mem (
        Ix 1 %% []
      ) (
        Apply (Opaque (setst_nm s k) %% [], ixi ~shift:1 (n + 1)) %% []
      ) %% []
    ) (
      ifx B.Conj (
        ifx B.Mem (Ix 1 %% []) (Ix (n + 2) %% []) %% []
      ) (
        body (* Dark magic; see Cook.relocalize *)
      ) %% []
    ) %% []
  ) %% []

let setof_def s n (TKind (ks, _) as k) body =
  let ss =
    let rec spin n ks =
      if n = 0 then ks
      else
        match ks with
        | TKind ([], TAtom TU) :: ks ->
            spin (n - 1) ks
        | _ -> invalid_arg ("Reduce.NtAxioms.setof_def: \
                              bad kind provided")
    in
    List.map (fun k -> get_atom (get_ty k)) (spin n ks)
  in
  let m = List.length ss in
  all (gen "s" n @ gen "a" m @ [ "y" ]) ~ss:(List.init n (fun i -> TU) @ ss @ [ TU ]) (
    ifx B.Equiv (
      ifx B.Mem (
        Ix 1 %% []
      ) (
        Apply (Opaque (setof_nm s n k) %% [], ixi ~shift:1 (m + n)) %% []
      ) %% []
    ) (
      exi (gen "x" n) (
        List (
          And,
          List.init n begin fun i ->
            ifx B.Mem (
              Ix (n - i) %% []
            ) (
              Ix (2*n + 1 + m - i) %% []
            ) %% []
          end
          @ [
            ifx B.Eq (
              Ix (n + 1) %% []
            ) (
              body (* Dark magic *)
            ) %% []
          ]
        ) %% []
      ) %% []
    ) %% []
  ) %% []

let subseteq_fact = mk_fact subseteq_def %% []
let enum_fact n = mk_fact (enum_def n) %% []
let union_fact = mk_fact union_def %% []
let power_fact = mk_fact power_def %% []
let cup_fact = mk_fact cup_def %% []
let cap_fact = mk_fact cap_def %% []
let setminus_fact = mk_fact setminus_def %% []
let setst_fact s k e = mk_fact (setst_def s k e) %% []
let setof_fact s n k e = mk_fact (setof_def s n k e) %% []


(* {3 Booleans} *)

let boolean_nm = nt_prefix ^ "Boolean"
let booltou_nm = nt_prefix ^ "bool_to_u"

let boolean_decl = mk_fresh boolean_nm [] TU %% []
let booltou_decl = mk_fresh booltou_nm [ TBool ] TU %% []

let boolean_def =
  all [ "x" ] (
    ifx B.Equiv (
      ifx B.Mem (Ix 1 %% []) (Internal B.BOOLEAN %% []) %% []
    ) (
      ifx B.Disj (
        ifx B.Eq (Ix 1 %% []) (
          Apply (Opaque booltou_nm %% [], [ Internal B.TRUE %% [] ]) %% []
        ) %% []
      ) (
        ifx B.Eq (Ix 1 %% []) (
          Apply (Opaque booltou_nm %% [], [ Internal B.FALSE %% [] ]) %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

let boolean_fact = mk_fact boolean_def %% []


(* {3 Strings} *)

let stringsort_nm = nt_prefix ^ "String"
let stringany_nm = nt_prefix ^ "any_string"

let string_nm = nt_prefix ^ "String"
let stringtou_nm = nt_prefix ^ "string_to_u"
let stringlit_nm s = nt_prefix ^ "string_lit_" ^ s

let stringany_decl = mk_fresh uany_nm [] TStr %% []

let string_decl = mk_fresh string_nm [] TU %% []
let stringtou_decl = mk_fresh stringtou_nm [ TStr ] TU %% []
let stringlit_decl s = mk_fresh (stringlit_nm s) [] TStr %% []

let string_def =
  all [ "x" ] (
    ifx B.Equiv (
      ifx B.Mem (Ix 1 %% []) (Internal B.STRING %% []) %% []
    ) (
      exi [ "s" ] ~ss:[ TStr ] (
        ifx B.Eq (
          Ix 2 %% []
        ) (
          Apply (Opaque stringtou_nm %% [], [ Ix 1 %% [] ]) %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

let stringcast_inj =
  all [ "s1" ; "s2" ] ~ss:[ TStr ; TStr ] (
    ifx B.Implies (
      ifx B.Eq (
        Apply (Opaque stringtou_nm %% [], [ Ix 2 %% [] ]) %% []
      ) (
        Apply (Opaque stringtou_nm %% [], [ Ix 1 %% [] ]) %% []
      ) %% []
    ) (
      ifx B.Eq (Ix 2 %% []) (Ix 1 %% []) %% []
    ) %% []
  ) %% []

let stringlit_distinct s1 s2 =
  ifx B.Neq (Opaque (stringlit_nm s1) %% []) (Opaque (stringlit_nm s2) %% []) %% []

let string_fact = mk_fact string_def %% []
let stringcast_fact = mk_fact stringcast_inj %% []
let stringlit_distinct_fact s1 s2 = mk_fact (stringlit_distinct s1 s2) %% []


(* {3 Functions} *)

let arrow_nm = nt_prefix ^ "Arrow"
let fcn_nm s _ = nt_prefix ^ "fcn_" ^ s
let domain_nm = nt_prefix ^ "domain"
let fcnapp_nm = nt_prefix ^ "fcnapp"
let fcnexcept_nm = nt_prefix ^ "fcnexcept"


(* {3 Arithmetic} *)

let zset_nm = nt_prefix ^ "Int"
let nset_nm = nt_prefix ^ "Nat"
let rset_nm = nt_prefix ^ "Real"
let plus_nm = nt_prefix ^ "plus"
let uminus_nm = nt_prefix ^ "uminus"
let minus_nm = nt_prefix ^ "minus"
let times_nm = nt_prefix ^ "times"
let ratio_nm = nt_prefix ^ "ratio"
let quotient_nm = nt_prefix ^ "quotient"
let remainder_nm = nt_prefix ^ "remainder"
let exp_nm = nt_prefix ^ "exp"
let infinity_nm = nt_prefix ^ "Infinity"
let lteq_nm = nt_prefix ^ "lteq"
let lt_nm = nt_prefix ^ "lt"
let gteq_nm = nt_prefix ^ "gteq"
let gt_nm = nt_prefix ^ "gt"
let range_nm = nt_prefix ^ "range"


(* {3 Tuples} *)

(* TODO *)


(* {3 Sequences} *)

(* TODO *)
