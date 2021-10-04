(*
 * encode/axioms.ml --- axioms for TLA+ symbols
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open Expr.T
open Type.T

open N_smb

module B = Builtin
module T = N_table


(* {3 Helpers} *)

let error ?at mssg =
  let mssg = "Encode.Axioms: " ^ mssg in
  (*Errors.bug ?at mssg*)
  failwith mssg

let t_idv = TAtm TAIdv
let t_bol = TAtm TABol
let t_int = TAtm TAInt
let t_str = TAtm TAStr

let maybe_assign prop =
  Option.fold (fun x -> assign x prop)

let app ?tys op es =
  let op = maybe_assign Props.tpars_prop op tys in
  match es with
  | [] -> Apply (op, []) (* Don't loose op properties *)
  | _ -> Apply (op, es)

let appb ?tys b es =
  app ?tys (Internal b %% []) es

let apps tla_smb es =
  let smb = mk_smb tla_smb in
  let opq = Opaque (get_name smb) %% [] in
  let opq = assign opq smb_prop smb in
  app opq es

let quant q xs ty0s ?pats e =
  if List.length xs > 0 then
    let xs =
      List.map2 begin fun x ty0 ->
        (assign (x %% []) Props.ty0_prop ty0, Constant, No_domain)
      end xs ty0s
    in
    let e = maybe_assign pattern_prop e pats in
    Quant (q, xs, e)
  else
    e.core

let lam xs ty0s e =
  let xs =
    List.map2 begin fun x ty0 ->
      (assign (x %% []) Props.ty0_prop ty0, Shape_expr)
    end xs ty0s
  in
  Lambda (xs, e)

let dupl a n = List.init n (fun _ -> a)

let gen x n = List.init n (fun i -> x ^ string_of_int (i + 1))
(** [gen "x" n] = [ "x1" ; .. ; "xn" ] *)

let ixi ?(shift=0) n = List.init n (fun i -> Ix (shift + n - i) %% [])
(** [ixi n]          = [ Ix n ; .. ; Ix 2 ; Ix 1 ]
    [ixi ~shift:s n] = [ Ix (s+n) ; .. ; Ix (s+2) ; Ix (s+1) ]
*)

let fresh x ty1 =
  let shp =
    match ty1 with
    | Ty1 ([], _) -> Shape_expr
    | Ty1 (ty0s, _) -> Shape_op (List.length ty0s)
  in
  let v = assign (x %% []) Props.ty2_prop (upcast_ty2 ty1) in
  Fresh (v, shp, Constant, Unbounded)

let seq xs ty1s e =
  let hs = List.map2 fresh xs ty1s in
  let hs = List.map noprops hs in
  Sequent { context = Deque.of_list hs ; active = e }


(* {3 Untyped/Monosorted Variants} *)

(* {4 Special} *)

let cast_inj ty0 =
  match ty0 with
  | TAtm TABol ->
      appb B.Conj
      [ appb ~tys:[ t_idv ] B.Eq
        [ apps (T.Cast t_bol)
          [ appb B.TRUE [] %% []
          ] %% []
        ; apps (T.True t_idv) [] %% []
        ] %% []
      ; appb ~tys:[ t_idv ] B.Neq
        [ apps (T.Cast t_bol)
          [ appb B.FALSE [] %% []
          ] %% []
        ; apps (T.True t_idv) [] %% []
        ] %% []
      ] %% []

  | _ ->
      quant Forall
      [ "x" ; "y" ] [ ty0 ; ty0 ]
      ~pats:[ [
        appb ~tys:[ t_idv ] B.Eq
        [ apps (T.Cast ty0)
          [ Ix 2 %% []
          ] %% []
        ; apps (T.Cast ty0)
          [ Ix 1 %% []
          ] %% []
        ] %% []
      ] ]
      ( appb B.Implies
        [ appb ~tys:[ t_idv ] B.Eq
          [ apps (T.Cast ty0)
            [ Ix 2 %% []
            ] %% []
          ; apps (T.Cast ty0)
            [ Ix 1 %% []
            ] %% []
          ] %% []
        ; appb ~tys:[ ty0 ] B.Eq
          [ Ix 2 %% []
          ; Ix 1 %% []
          ] %% []
        ] %% []
      ) %% []

let type_guard ty0 =
  quant Forall
  [ "x" ] [ t_idv ]
  ( appb B.Equiv
    [ begin match ty0 with
    | TAtm TAIdv ->
        appb B.TRUE [] %% []
    | TAtm TABol ->
        apps T.Mem
        [ Ix 1 %% []
        ; apps T.BoolSet [] %% []
        ] %% []
    | TAtm TAInt ->
        apps T.Mem
        [ Ix 1 %% []
        ; apps T.IntSet [] %% []
        ] %% []
    | TAtm TAStr ->
        apps T.Mem
        [ Ix 1 %% []
        ; apps T.StrSet [] %% []
        ] %% []
    | _ -> error "Not implemented"
    end
    ; quant Exists
      [ "y" ] [ ty0 ]
      ( appb ~tys:[ t_idv ] B.Eq
        [ Ix 2 %% []
        ; apps (T.Cast ty0)
          [ Ix 1 %% []
          ] %% []
        ] %% []
      ) %% []
    ] %% []
  ) %% []

let op_typing t_smb =
  let t_dat = N_data.get_data t_smb in
  let i_smb = Option.get (t_dat.dat_tver) in
  let i_dat = N_data.get_data i_smb in

  let i_ty2 = i_dat.dat_ty2 in
  let t_ty2 = t_dat.dat_ty2 in

  (* It is assumed that i_ty2 is obtained from t_ty2 by replacing every sort
   * other than Bool with Idv, and possibly some occurrences of Bool with Idv
   * (but not necessarily all). *)
  (* TODO: Support second-order shapes *)

  let Ty1 (_, i_ty0) =
    try downcast_ty1 i_ty2
    with _ -> error "Not implemented"
  in
  let Ty1 (t_ty0s, t_ty0) =
    try downcast_ty1 t_ty2
    with _ -> error "Not implemented"
  in

  let cast ty_from e =
    if ty_from = t_idv then e
    else apps (T.Cast ty_from) [ e ] %% []
  in
  let proj ty_from e =
    if ty_from = t_bol then e
    else
      appb ~tys:[ ty_from ] B.Eq
      [ e
      ; apps (T.True ty_from) [] %% []
      ] %% []
  in

  let n = List.length t_ty0s in
  let is_pred = (t_ty0 = t_bol) in

  quant Forall
  (gen "x" n) t_ty0s
  ~pats:[ [
    apps i_smb
    (List.map2 begin fun e ty0 ->
      cast ty0 e
    end (ixi n) t_ty0s) %% []
  ] ]
  ( begin
      if is_pred then appb B.Equiv
      else appb ~tys:[ t_idv ] B.Eq
    end
    [ apps i_smb
      (List.map2 begin fun e ty0 ->
        cast ty0 e
      end (ixi n) t_ty0s) %% [] |>
      begin
        if is_pred then proj i_ty0
        else fun e -> e
      end
    ; apps t_smb
      (ixi n) %% [] |>
      begin
        if is_pred then fun e -> e
        else cast t_ty0
      end
    ] %% []
  ) %% []


(* {4 Logic} *)

let choose_def () =
  seq
  [ "P" ]
  [ Ty1 ([ t_idv ], t_bol) ]
  ( quant Forall
    [ "x" ] [ t_idv ]
    ~pats:[ [
      app (Ix 2 %% [])
      [ Ix 1 %% []
      ] %% []
    ] ]
    ( appb B.Implies
      [ app (Ix 2 %% [])
        [ Ix 1 %% []
        ] %% []
      ; app (Ix 2 %% [])
        [ apps T.Choose
          [ Ix 2 %% []
          ] %% []
        ] %% []
      ] %% []
    ) %% []
  ) %% []

let choose_ext () =
  seq
  [ "P" ; "Q" ]
  (dupl (Ty1 ([ t_idv ], t_bol)) 2)
  ( appb B.Implies
    [ quant Forall
      [ "x" ] [ t_idv ]
      ( appb B.Equiv
        [ app (Ix 3 %% [])
          [ Ix 1 %% []
          ] %% []
        ; app (Ix 2 %% [])
          [ Ix 1 %% []
          ] %% []
        ] %% []
      ) %% []
    ; appb ~tys:[ t_idv ] B.Eq
      [ apps T.Choose
        [ Ix 2 %% []
        ] %% []
      ; apps T.Choose
        [ Ix 1 %% []
        ] %% []
      ] %% []
    ] %% []
  ) %% []

(* {4 Sets} *)

let set_ext () =
  quant Forall
  [ "x" ; "y" ] [ t_idv ; t_idv ]
  ( appb B.Implies
    [ quant Forall
      [ "z" ] [ t_idv ]
      ( appb B.Equiv
        [ apps T.Mem
          [ Ix 1 %% []
          ; Ix 3 %% []
          ] %% []
        ; apps T.Mem
          [ Ix 1 %% []
          ; Ix 2 %% []
          ] %% []
        ] %% []
      ) %% []
    ; appb ~tys:[ t_idv ] B.Eq
      [ Ix 2 %% []
      ; Ix 1 %% []
      ] %% []
    ] %% []
  ) %% []

let subseteq_def () =
  quant Forall
  [ "x" ; "y" ] [ t_idv ; t_idv ]
  ~pats:[ [
    apps T.SubsetEq
    [ Ix 2 %% []
    ; Ix 1 %% []
    ] %% []
  ] ]
  ( appb B.Equiv
    [ apps T.SubsetEq
      [ Ix 2 %% []
      ; Ix 1 %% []
      ] %% []
    ; quant Forall
      [ "z" ] [ t_idv ]
      ( appb B.Implies
        [ apps T.Mem
          [ Ix 1 %% []
          ; Ix 3 %% []
          ] %% []
        ; apps T.Mem
          [ Ix 1 %% []
          ; Ix 2 %% []
          ] %% []
        ] %% []
      ) %% []
    ] %% []
  ) %% []

let subseteq_intro () =
  quant Forall
  [ "x" ; "y" ] [ t_idv ; t_idv ]
  ~pats:[ [
    apps T.SubsetEq
    [ Ix 2 %% []
    ; Ix 1 %% []
    ] %% []
  ] ]
  ( appb B.Implies
    [ quant Forall
      [ "z" ] [ t_idv ]
      ( appb B.Implies
        [ apps T.Mem
          [ Ix 1 %% []
          ; Ix 3 %% []
          ] %% []
        ; apps T.Mem
          [ Ix 1 %% []
          ; Ix 2 %% []
          ] %% []
        ] %% []
      ) %% []
    ; apps T.SubsetEq
      [ Ix 2 %% []
      ; Ix 1 %% []
      ] %% []
    ] %% []
  ) %% []

let subseteq_elim () =
  quant Forall
  [ "x" ; "y" ; "z" ] [ t_idv ; t_idv ; t_idv ]
  ~pats:[ [
    apps T.SubsetEq
    [ Ix 3 %% []
    ; Ix 2 %% []
    ] %% []
  ; apps T.Mem
    [ Ix 1 %% []
    ; Ix 3 %% []
    ] %% []
  ] ]
  ( appb B.Implies
    [ appb B.Conj
      [ apps T.SubsetEq
        [ Ix 3 %% []
        ; Ix 2 %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; Ix 3 %% []
        ] %% []
      ] %% []
    ; apps T.Mem
      [ Ix 1 %% []
      ; Ix 2 %% []
      ] %% []
    ] %% []
  ) %% []

let setenum_def n =
  quant Forall
  (gen "a" n @ [ "x" ]) (dupl t_idv (n+1))
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps (T.SetEnum n)
      (ixi ~shift:1 n) %% []
    ] %% []
  ] ]
  begin if (n = 0) then
    appb B.Neg
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps (T.SetEnum 0) [] %% []
      ] %% []
    ] %% []
  else
    appb B.Equiv
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps (T.SetEnum n)
        (ixi ~shift:1 n) %% []
      ] %% []
    ; List.init n begin fun i ->
        appb ~tys:[ t_idv ] B.Eq
        [ Ix 1 %% []
        ; Ix (n-i+1) %% []
        ] %% []
      end |>
      function
        | [e] -> e
        | es -> List (Or, es) %% []
    ] %% []
  end %% []

let setenum_intro n =
  quant Forall
  (gen "a" n @ [ "x" ]) (dupl t_idv (n+1))
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps (T.SetEnum n)
      (ixi ~shift:1 n) %% []
    ] %% []
  ] ]
  begin if (n = 0) then
    appb B.Neg
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps (T.SetEnum 0) [] %% []
      ] %% []
    ] %% []
  else
    appb B.Implies
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps (T.SetEnum n)
        (ixi ~shift:1 n) %% []
      ] %% []
    ; List.init n begin fun i ->
        appb ~tys:[ t_idv ] B.Eq
        [ Ix 1 %% []
        ; Ix (n-i+1) %% []
        ] %% []
      end |>
      function
        | [e] -> e
        | es -> List (Or, es) %% []
    ] %% []
  end %% []

let setenum_elim n =
  quant Forall
  (gen "a" n) (dupl t_idv n)
  ~pats:[ [
    apps (T.SetEnum n)
    (ixi n) %% []
  ] ]
  begin if (n = 0) then
    Internal B.TRUE %% []
  else
    List.init n begin fun i ->
      apps T.Mem
      [ Ix (n-i) %% []
      ; apps (T.SetEnum n)
        (ixi n) %% []
      ] %% []
    end |>
    function
      | [e] -> e
      | es -> List (And, es) %% []
  end %% []

let union_def () =
  quant Forall
  [ "a" ; "x" ] [ t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps T.Union
      [ Ix 2 %% []
      ] %% []
    ] %% []
  ] ]
  ( appb B.Equiv
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps T.Union
        [ Ix 2 %% []
        ] %% []
      ] %% []
    ; quant Exists
      [ "y" ] [ t_idv ]
      ( appb B.Conj
        [ apps T.Mem
          [ Ix 1 %% []
          ; Ix 3 %% []
          ] %% []
        ; apps T.Mem
          [ Ix 2 %% []
          ; Ix 1 %% []
          ] %% []
        ] %% []
      ) %% []
    ] %% []
  ) %% []

let union_intro () =
  quant Forall
  [ "a" ; "x" ; "y" ] [ t_idv ; t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; Ix 3 %% []
    ] %% []
  ; apps T.Mem
    [ Ix 2 %% []
    ; Ix 1 %% []
    ] %% []
  ] ; [
    apps T.Mem
    [ Ix 1 %% []
    ; Ix 3 %% []
    ] %% []
  ; apps T.Mem
    [ Ix 2 %% []
    ; apps T.Union
      [ Ix 3 %% []
      ] %% []
    ] %% []
  ] ; [
    apps T.Mem
    [ Ix 2 %% []
    ; Ix 1 %% []
    ] %% []
  ; apps T.Mem
    [ Ix 2 %% []
    ; apps T.Union
      [ Ix 3 %% []
      ] %% []
    ] %% []
  ] ]
  ( appb B.Implies
    [ appb B.Conj
      [ apps T.Mem
        [ Ix 1 %% []
        ; Ix 3 %% []
        ] %% []
      ; apps T.Mem
        [ Ix 2 %% []
        ; Ix 1 %% []
        ] %% []
      ] %% []
    ; apps T.Mem
      [ Ix 2 %% []
      ; apps T.Union
        [ Ix 3 %% []
        ] %% []
      ] %% []
    ] %% []
  ) %% []

let union_elim () =
  quant Forall
  [ "a" ; "x" ] [ t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps T.Union
      [ Ix 2 %% []
      ] %% []
    ] %% []
  ] ]
  ( appb B.Implies
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps T.Union
        [ Ix 2 %% []
        ] %% []
      ] %% []
    ; quant Exists
      [ "y" ] [ t_idv ]
      ( appb B.Conj
        [ apps T.Mem
          [ Ix 1 %% []
          ; Ix 3 %% []
          ] %% []
        ; apps T.Mem
          [ Ix 2 %% []
          ; Ix 1 %% []
          ] %% []
        ] %% []
      ) %% []
    ] %% []
  ) %% []

let subset_def () =
  quant Forall
  [ "a" ; "x" ] [ t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps T.Subset
      [ Ix 2 %% []
      ] %% []
    ] %% []
  ] ]
  ( appb B.Equiv
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps T.Subset
        [ Ix 2 %% []
        ] %% []
      ] %% []
    ; quant Forall
      [ "y" ] [ t_idv ]
      ( appb B.Implies
        [ apps T.Mem
          [ Ix 1 %% []
          ; Ix 2 %% []
          ] %% []
        ; apps T.Mem
          [ Ix 1 %% []
          ; Ix 3 %% []
          ] %% []
        ] %% []
      ) %% []
    ] %% []
  ) %% []

let subset_intro () =
  quant Forall
  [ "a" ; "x" ] [ t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps T.Subset
      [ Ix 2 %% []
      ] %% []
    ] %% []
  ] ]
  ( appb B.Implies
    [ quant Forall
      [ "y" ] [ t_idv ]
      ( appb B.Implies
        [ apps T.Mem
          [ Ix 1 %% []
          ; Ix 2 %% []
          ] %% []
        ; apps T.Mem
          [ Ix 1 %% []
          ; Ix 3 %% []
          ] %% []
        ] %% []
      ) %% []
    ; apps T.Mem
      [ Ix 1 %% []
      ; apps T.Subset
        [ Ix 2 %% []
        ] %% []
      ] %% []
    ] %% []
  ) %% []

let subset_elim () =
  quant Forall
  [ "a" ; "x" ; "y" ] [ t_idv ; t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 2 %% []
    ; apps T.Subset
      [ Ix 3 %% []
      ] %% []
    ] %% []
  ; apps T.Mem
    [ Ix 1 %% []
    ; Ix 2 %% []
    ] %% []
  ] ; [
    apps T.Mem
    [ Ix 2 %% []
    ; apps T.Subset
      [ Ix 3 %% []
      ] %% []
    ] %% []
  ; apps T.Mem
    [ Ix 1 %% []
    ; Ix 3 %% []
    ] %% []
  ] ]
  ( appb B.Implies
    [ appb B.Conj
      [ apps T.Mem
        [ Ix 2 %% []
        ; apps T.Subset
          [ Ix 3 %% []
          ] %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; Ix 2 %% []
        ] %% []
      ] %% []
    ; apps T.Mem
      [ Ix 1 %% []
      ; Ix 3 %% []
      ] %% []
    ] %% []
  ) %% []

let cup_def () =
  quant Forall
  [ "a" ; "b" ; "x" ] [ t_idv ; t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps T.Cup
      [ Ix 3 %% []
      ; Ix 2 %% []
      ] %% []
    ] %% []
  ] ]
  ( appb B.Equiv
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps T.Cup
        [ Ix 3 %% []
        ; Ix 2 %% []
        ] %% []
      ] %% []
    ; appb B.Disj
      [ apps T.Mem
        [ Ix 1 %% []
        ; Ix 3 %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; Ix 2 %% []
        ] %% []
      ] %% []
    ] %% []
  ) %% []

let cap_def () =
  quant Forall
  [ "a" ; "b" ; "x" ] [ t_idv ; t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps T.Cap
      [ Ix 3 %% []
      ; Ix 2 %% []
      ] %% []
    ] %% []
  ] ]
  ( appb B.Equiv
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps T.Cap
        [ Ix 3 %% []
        ; Ix 2 %% []
        ] %% []
      ] %% []
    ; appb B.Conj
      [ apps T.Mem
        [ Ix 1 %% []
        ; Ix 3 %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; Ix 2 %% []
        ] %% []
      ] %% []
    ] %% []
  ) %% []

let setminus_def () =
  quant Forall
  [ "a" ; "b" ; "x" ] [ t_idv ; t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps T.SetMinus
      [ Ix 3 %% []
      ; Ix 2 %% []
      ] %% []
    ] %% []
  ] ]
  ( appb B.Equiv
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps T.SetMinus
        [ Ix 3 %% []
        ; Ix 2 %% []
        ] %% []
      ] %% []
    ; appb B.Conj
      [ apps T.Mem
        [ Ix 1 %% []
        ; Ix 3 %% []
        ] %% []
      ; appb B.Neg
        [ apps T.Mem
          [ Ix 1 %% []
          ; Ix 2 %% []
          ] %% []
        ] %% []
      ] %% []
    ] %% []
  ) %% []

let setst_def () =
  seq
  [ "P" ]
  [ Ty1 ([ t_idv ], t_bol) ]
  ( quant Forall
    [ "a" ; "x" ] [ t_idv ; t_idv ]
    ~pats:[ [
      apps T.Mem
      [ Ix 1 %% []
      ; apps T.SetSt
        [ Ix 2 %% []
        ; Ix 3 %% []
        ] %% []
      ] %% []
    ] ]
    ( appb B.Equiv
      [ apps T.Mem
        [ Ix 1 %% []
        ; apps T.SetSt
          [ Ix 2 %% []
          ; Ix 3 %% []
          ] %% []
        ] %% []
      ; appb B.Conj
        [ apps T.Mem
          [ Ix 1 %% []
          ; Ix 2 %% []
          ] %% []
        ; app (Ix 3 %% [])
          [ Ix 1 %% []
          ] %% []
        ] %% []
      ] %% []
    ) %% []
  ) %% []

let setof_def n =
  seq
  [ "F" ]
  [ Ty1 (dupl t_idv n, t_idv) ]
  ( quant Forall
    (gen "a" n @ [ "x" ]) (dupl t_idv (n+1))
    ~pats:[ [
      apps T.Mem
      [ Ix 1 %% []
      ; apps (T.SetOf n)
        (List.init n begin fun i ->
          Ix (n-i+1) %% []
        end @
        [ Ix (n+2) %% []
        ]) %% []
      ] %% []
    ] ]
    ( appb B.Equiv
      [ apps T.Mem
        [ Ix 1 %% []
        ; apps (T.SetOf n)
          (List.init n begin fun i ->
            Ix (n-i+1) %% []
          end @
          [ Ix (n+2) %% []
          ]) %% []
        ] %% []
      ; quant Exists
        (gen "y" n) (dupl t_idv n)
        ( List (And,
            List.init n begin fun i ->
              apps T.Mem
              [ Ix (n-i) %% []
              ; Ix (2*n-i+1) %% []
              ] %% []
            end @
            [ appb ~tys:[ t_idv ] B.Eq
              [ Ix (n+1) %% []
              ; app (Ix (2*n+2) %% [])
                (ixi n) %% []
              ] %% []
            ]
          ) %% []
        ) %% []
      ] %% []
    ) %% []
  ) %% []

let setof_intro n =
  seq
  [ "F" ]
  [ Ty1 (dupl t_idv n, t_idv) ]
  ( quant Forall
    (gen "a" n @ gen "y" n) (dupl t_idv (n+n))
    ~pats:[ [
      apps T.Mem
      [ app (Ix (2*n+1) %% [])
        (ixi n) %% []
      ; apps (T.SetOf n)
        (List.init n begin fun i ->
          Ix (n-i+1) %% []
        end @
        [ Ix (n+2) %% []
        ]) %% []
      ] %% []
    ] ]
    ( appb B.Implies
      [ List (And,
          List.init n begin fun i ->
            apps T.Mem
            [ Ix (n-i) %% []
            ; Ix (2*n-i) %% []
            ] %% []
          end
        ) %% []
      ; apps T.Mem
        [ app (Ix (2*n+1) %% [])
          (ixi n) %% []
        ; apps (T.SetOf n)
          (List.init n begin fun i ->
            Ix (n-i+1) %% []
          end @
          [ Ix (n+2) %% []
          ]) %% []
        ] %% []
      ] %% []
    ) %% []
  ) %% []

let setof_elim n =
  seq
  [ "F" ]
  [ Ty1 (dupl t_idv n, t_idv) ]
  ( quant Forall
    (gen "a" n @ [ "x" ]) (dupl t_idv (n+1))
    ~pats:[ [
      apps T.Mem
      [ Ix 1 %% []
      ; apps (T.SetOf n)
        (List.init n begin fun i ->
          Ix (n-i+1) %% []
        end @
        [ Ix (n+2) %% []
        ]) %% []
      ] %% []
    ] ]
    ( appb B.Implies
      [ apps T.Mem
        [ Ix 1 %% []
        ; apps (T.SetOf n)
          (List.init n begin fun i ->
            Ix (n-i+1) %% []
          end @
          [ Ix (n+2) %% []
          ]) %% []
        ] %% []
      ; quant Exists
        (gen "y" n) (dupl t_idv n)
        ( List (And,
            List.init n begin fun i ->
              apps T.Mem
              [ Ix (n-i) %% []
              ; Ix (2*n-i+1) %% []
              ] %% []
            end @
            [ appb ~tys:[ t_idv ] B.Eq
              [ Ix (n+1) %% []
              ; app (Ix (2*n+2) %% [])
                (ixi n) %% []
              ] %% []
            ]
          ) %% []
        ) %% []
      ] %% []
    ) %% []
  ) %% []


(* {4 Functions} *)

(* {3 Functions - Base Axioms} *)

let fcn_ext () =
  quant Forall
  [ "f" ; "g" ] [ t_idv ; t_idv ]
  ~pats:[ [
    apps T.FunIsafcn
    [ Ix 2 %% []
    ] %% []
  ; apps T.FunIsafcn
    [ Ix 1 %% []
    ] %% []
  ] ]
  ( appb B.Implies
    [ List (And,
      [ apps T.FunIsafcn
        [ Ix 2 %% []
        ] %% []
      ; apps T.FunIsafcn
        [ Ix 1 %% []
        ] %% []
      ; appb ~tys:[ t_idv ] B.Eq
        [ apps T.FunDom
          [ Ix 2 %% []
          ] %% []
        ; apps T.FunDom
          [ Ix 1 %% []
          ] %% []
        ] %% []
      ; quant Forall
        [ "x" ] [ t_idv ]
        ( appb B.Implies
          [ apps T.Mem
            [ Ix 1 %% []
            ; apps T.FunDom
              [ Ix 3 %% []
              ] %% []
            ] %% []
          ; appb ~tys:[ t_idv ] B.Eq
            [ apps T.FunApp
              [ Ix 3 %% []
              ; Ix 1 %% []
              ] %% []
            ; apps T.FunApp
              [ Ix 2 %% []
              ; Ix 1 %% []
              ] %% []
            ] %% []
          ] %% []
        ) %% []
      ]) %% []
    ; appb ~tys:[ t_idv ] B.Eq
      [ Ix 2 %% []
      ; Ix 1 %% []
      ] %% []
    ] %% []
  ) %% []

let fcnconstr_isafcn () =
  seq
  [ "F" ] [ Ty1 ([ t_idv ], t_idv) ]
  ( quant Forall
    ~pats:[ [
      apps T.FunConstr
      [ Ix 1 %% []
      ; Ix 2 %% []
      ] %% []
    ] ]
    [ "a" ] [ t_idv ]
    ( apps T.FunIsafcn
      [ apps T.FunConstr
        [ Ix 1 %% []
        ; Ix 2 %% []
        ] %% []
      ] %% []
    ) %% []
  ) %% []

let fcnset_def () =
  quant Forall
  [ "a" ; "b" ; "f" ] [ t_idv ; t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps T.FunSet
      [ Ix 3 %% []
      ; Ix 2 %% []
      ] %% []
    ] %% []
  ] ]
  ( appb B.Equiv
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps T.FunSet
        [ Ix 3 %% []
        ; Ix 2 %% []
        ] %% []
      ] %% []
    ; List (And,
      [ apps T.FunIsafcn
        [ Ix 1 %% []
        ] %% []
      ; appb ~tys:[ t_idv ] B.Eq
        [ apps T.FunDom
          [ Ix 1 %% []
          ] %% []
        ; Ix 3 %% []
        ] %% []
      ; quant Forall
        [ "x" ] [ t_idv ]
        ( appb B.Implies
          [ apps T.Mem
            [ Ix 1 %% []
            ; Ix 4 %% []
            ] %% []
          ; apps T.Mem
            [ apps T.FunApp
              [ Ix 2 %% []
              ; Ix 1 %% []
              ] %% []
            ; Ix 3 %% []
            ] %% []
          ] %% []
        ) %% []
      ]) %% []
    ] %% []
  ) %% []

let fcnset_intro () =
  quant Forall
  [ "a" ; "b" ; "f" ] [ t_idv ; t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps T.FunSet
      [ Ix 3 %% []
      ; Ix 2 %% []
      ] %% []
    ] %% []
  ] ]
  ( appb B.Implies
    [ List (And,
      [ apps T.FunIsafcn
        [ Ix 1 %% []
        ] %% []
      ; appb ~tys:[ t_idv ] B.Eq
        [ apps T.FunDom
          [ Ix 1 %% []
          ] %% []
        ; Ix 3 %% []
        ] %% []
      ; quant Forall
        [ "x" ] [ t_idv ]
        ( appb B.Implies
          [ apps T.Mem
            [ Ix 1 %% []
            ; Ix 4 %% []
            ] %% []
          ; apps T.Mem
            [ apps T.FunApp
              [ Ix 2 %% []
              ; Ix 1 %% []
              ] %% []
            ; Ix 3 %% []
            ] %% []
          ] %% []
        ) %% []
      ]) %% []
    ; apps T.Mem
      [ Ix 1 %% []
      ; apps T.FunSet
        [ Ix 3 %% []
        ; Ix 2 %% []
        ] %% []
      ] %% []
    ] %% []
  ) %% []

let fcnset_elim1 () =
  quant Forall
  [ "a" ; "b" ; "f" ] [ t_idv ; t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps T.FunSet
      [ Ix 3 %% []
      ; Ix 2 %% []
      ] %% []
    ] %% []
  ] ]
  ( appb B.Implies
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps T.FunSet
        [ Ix 3 %% []
        ; Ix 2 %% []
        ] %% []
      ] %% []
    ; appb B.Conj
      [ apps T.FunIsafcn
        [ Ix 1 %% []
        ] %% []
      ; appb ~tys:[ t_idv ] B.Eq
        [ apps T.FunDom
          [ Ix 1 %% []
          ] %% []
        ; Ix 3 %% []
        ] %% []
      ] %% []
    ] %% []
  ) %% []

let fcnset_elim2 () =
  quant Forall
  [ "a" ; "b" ; "f" ; "x" ] [ t_idv ; t_idv ; t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 2 %% []
    ; apps T.FunSet
      [ Ix 4 %% []
      ; Ix 3 %% []
      ] %% []
    ] %% []
  ; apps T.Mem
    [ Ix 1 %% []
    ; Ix 4 %% []
    ] %% []
  ] ; [
    apps T.Mem
    [ Ix 2 %% []
    ; apps T.FunSet
      [ Ix 4 %% []
      ; Ix 3 %% []
      ] %% []
    ] %% []
  ; apps T.FunApp
    [ Ix 2 %% []
    ; Ix 1 %% []
    ] %% []
  ] ]
  ( appb B.Implies
    [ appb B.Conj
      [ apps T.Mem
        [ Ix 2 %% []
        ; apps T.FunSet
          [ Ix 4 %% []
          ; Ix 3 %% []
          ] %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; Ix 4 %% []
        ] %% []
      ] %% []
    ; apps T.Mem
      [ apps T.FunApp
        [ Ix 2 %% []
        ; Ix 1 %% []
        ] %% []
      ; Ix 3 %% []
      ] %% []
    ] %% []
  ) %% []

let fcndom_def () =
  seq
  [ "F" ] [ Ty1 ([ t_idv ], t_idv) ]
  ( quant Forall
    [ "a" ] [ t_idv ]
    ~pats:[ [
      apps T.FunDom
      [ apps T.FunConstr
        [ Ix 1 %% []
        ; Ix 2 %% []
        ] %% []
      ] %% []
    ] ]
    ( appb ~tys:[ t_idv ] B.Eq
      [ apps T.FunDom
        [ apps T.FunConstr
          [ Ix 1 %% []
          ; Ix 2 %% []
          ] %% []
        ] %% []
      ; Ix 1 %% []
      ] %% []
    ) %% []
  ) %% []

let fcnapp_def () =
  seq
  [ "F" ] [ Ty1 ([ t_idv ], t_idv) ]
  ( quant Forall
    [ "a" ; "x" ] [ t_idv ; t_idv ]
    ~pats:[ [
      apps T.FunApp
      [ apps T.FunConstr
        [ Ix 2 %% []
        ; Ix 3 %% []
        ] %% []
      ; Ix 1 %% []
      ] %% []
    ] ]
    ( appb B.Implies
      [ apps T.Mem
        [ Ix 1 %% []
        ; Ix 2 %% []
        ] %% []
      ; appb ~tys:[ t_idv ] B.Eq
        [ apps T.FunApp
          [ apps T.FunConstr
            [ Ix 2 %% []
            ; Ix 3 %% []
            ] %% []
          ; Ix 1 %% []
          ] %% []
        ; app (Ix 3 %% [])
          [ Ix 1 %% []
          ] %% []
        ] %% []
      ] %% []
    ) %% []
  ) %% []

let fcnexcept_isafcn () =
  quant Forall
  [ "f" ; "x" ; "y" ] [ t_idv ; t_idv ; t_idv ]
  ~pats:[ [
    apps T.FunExcept
    [ Ix 3 %% []
    ; Ix 2 %% []
    ; Ix 1 %% []
    ] %% []
  ] ]
  ( apps T.FunIsafcn
    [ apps T.FunExcept
      [ Ix 3 %% []
      ; Ix 2 %% []
      ; Ix 1 %% []
      ] %% []
    ] %% []
  ) %% []

let fcnexceptdom_def () =
  quant Forall
  [ "f" ; "x" ; "y" ] [ t_idv ; t_idv ; t_idv ]
  ~pats:[ [
    apps T.FunExcept
    [ Ix 3 %% []
    ; Ix 2 %% []
    ; Ix 1 %% []
    ] %% []
  ] ]
  ( appb ~tys:[ t_idv ] B.Eq
    [ apps T.FunDom
      [ apps T.FunExcept
        [ Ix 3 %% []
        ; Ix 2 %% []
        ; Ix 1 %% []
        ] %% []
      ] %% []
    ; apps T.FunDom
      [ Ix 3 %% []
      ] %% []
    ] %% []
  ) %% []

let fcnexceptapp_def () =
  quant Forall
  [ "f" ; "x" ; "y" ; "z" ] [ t_idv ; t_idv ; t_idv ; t_idv ]
  ~pats:[ [
    apps T.FunApp
    [ apps T.FunExcept
      [ Ix 4 %% []
      ; Ix 3 %% []
      ; Ix 2 %% []
      ] %% []
    ; Ix 1 %% []
    ] %% []
  ] ]
  ( appb B.Implies
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps T.FunDom
        [ Ix 4 %% []
        ] %% []
      ] %% []
    ; appb B.Conj
      [ appb B.Implies
        [ appb ~tys:[ t_idv ] B.Eq
          [ Ix 1 %% []
          ; Ix 3 %% []
          ] %% []
        ; appb ~tys:[ t_idv ] B.Eq
          [ apps T.FunApp
            [ apps T.FunExcept
              [ Ix 4 %% []
              ; Ix 3 %% []
              ; Ix 2 %% []
              ] %% []
            ; Ix 1 %% []
            ] %% []
          ; Ix 2 %% []
          ] %% []
        ] %% []
      ; appb B.Implies
        [ appb ~tys:[ t_idv ] B.Neq
          [ Ix 1 %% []
          ; Ix 3 %% []
          ] %% []
        ; appb ~tys:[ t_idv ] B.Eq
          [ apps T.FunApp
            [ apps T.FunExcept
              [ Ix 4 %% []
              ; Ix 3 %% []
              ; Ix 2 %% []
              ] %% []
            ; Ix 1 %% []
            ] %% []
          ; apps T.FunApp
            [ Ix 4 %% []
            ; Ix 1 %% []
            ] %% []
          ] %% []
        ] %% []
      ] %% []
    ] %% []
  ) %% []


(* {4 Strings} *)

let strlit_isstr s =
  apps T.Mem
  [ apps (T.StrLit s) [] %% []
  ; apps T.StrSet [] %% []
  ] %% []

let strlit_distinct s1 s2 =
  appb ~tys:[ t_idv ] B.Neq
  [ apps (T.StrLit s1) [] %% []
  ; apps (T.StrLit s2) [] %% []
  ] %% []


(* {4 Arithmetic} *)

let natset_def ~noarith =
  quant Forall
  [ "x" ] [ t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps T.NatSet [] %% []
    ] %% []
  ] ]
  ( appb B.Equiv
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps T.NatSet [] %% []
      ] %% []
    ; appb B.Conj
      [ apps T.Mem
        [ Ix 1 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; apps T.IntLteq
        [ begin
          if noarith then
            apps (T.IntLit 0) [] %% []
          else
            apps (T.Cast t_int)
            [ apps (T.TIntLit 0) [] %% []
            ] %% []
          end
        ; Ix 1 %% []
        ] %% []
      ] %% []
    ] %% []
  ) %% []

(* NOTE According to Specifying Systems, the definition is:
 *     a..b == { i \in Int : a <= i /\ i <= b }
 * By this definition it is not required that a, b \in Int
 *)
let intrange_def () =
  quant Forall
  [ "a" ; "b" ; "x" ] [ t_idv ; t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps T.IntRange
      [ Ix 3 %% []
      ; Ix 2 %% []
      ] %% []
    ] %% []
  ] ]
  ( (*appb B.Implies
    [ appb B.Conj
      [ apps T.Mem
        [ Ix 3 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; apps T.Mem
        [ Ix 2 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ] %% []
    ;*) appb B.Equiv
      [ apps T.Mem
        [ Ix 1 %% []
        ; apps T.IntRange
          [ Ix 3 %% []
          ; Ix 2 %% []
          ] %% []
        ] %% []
      ; List (And,
        [ apps T.Mem
          [ Ix 1 %% []
          ; apps T.IntSet [] %% []
          ] %% []
        ; apps T.IntLteq
          [ Ix 3 %% []
          ; Ix 1 %% []
          ] %% []
        ; apps T.IntLteq
          [ Ix 1 %% []
          ; Ix 2 %% []
          ] %% []
        ]) %% []
      ] %% []
    (*] %% []*)
  ) %% []

let intlit_isint n =
  apps T.Mem
  [ apps (T.IntLit n) [] %% []
  ; apps T.IntSet [] %% []
  ] %% []

let intlit_distinct m n =
  appb ~tys:[ t_idv ] B.Neq
  [ apps (T.IntLit m) [] %% []
  ; apps (T.IntLit n) [] %% []
  ] %% []

let intlit_zerocmp n =
  if n <= 0 then
    apps T.IntLteq
    [ apps (T.IntLit n) [] %% []
    ; apps (T.IntLit 0) [] %% []
    ] %% []
  else
    apps T.IntLteq
    [ apps (T.IntLit 0) [] %% []
    ; apps (T.IntLit n) [] %% []
    ] %% []

let intplus_typing () =
  quant Forall
  [ "x" ; "y" ] [ t_idv ; t_idv ]
  ( appb B.Implies
    [ appb B.Conj
      [ apps T.Mem
        [ Ix 2 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ] %% []
    ; apps T.Mem
      [ apps T.IntPlus
        [ Ix 2 %% []
        ; Ix 1 %% []
        ] %% []
      ; apps T.IntSet [] %% []
      ] %% []
    ] %% []
  ) %% []

let intuminus_typing () =
  quant Forall
  [ "x" ] [ t_idv ]
  ( appb B.Implies
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps T.IntSet [] %% []
      ] %% []
    ; apps T.Mem
      [ apps T.IntUminus
        [ Ix 1 %% []
        ] %% []
      ; apps T.IntSet [] %% []
      ] %% []
    ] %% []
  ) %% []

let intminus_typing () =
  quant Forall
  [ "x" ; "y" ] [ t_idv ; t_idv ]
  ( appb B.Implies
    [ appb B.Conj
      [ apps T.Mem
        [ Ix 2 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ] %% []
    ; apps T.Mem
      [ apps T.IntMinus
        [ Ix 2 %% []
        ; Ix 1 %% []
        ] %% []
      ; apps T.IntSet [] %% []
      ] %% []
    ] %% []
  ) %% []

let inttimes_typing () =
  quant Forall
  [ "x" ; "y" ] [ t_idv ; t_idv ]
  ( appb B.Implies
    [ appb B.Conj
      [ apps T.Mem
        [ Ix 2 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ] %% []
    ; apps T.Mem
      [ apps T.IntTimes
        [ Ix 2 %% []
        ; Ix 1 %% []
        ] %% []
      ; apps T.IntSet [] %% []
      ] %% []
    ] %% []
  ) %% []

let intexp_typing () =
  quant Forall
  [ "x" ; "y" ] [ t_idv ; t_idv ]
  ( appb B.Implies
    [ List (And,
      [ apps T.Mem
        [ Ix 2 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; appb ~tys:[ t_idv ] B.Neq
        [ Ix 2 %% []
          (* This axiom is only used when noarith = true *)
        ; apps (T.IntLit 0) [] %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ]) %% []
    ; apps T.Mem
      [ apps T.IntExp
        [ Ix 2 %% []
        ; Ix 1 %% []
        ] %% []
      ; apps T.IntSet [] %% []
      ] %% []
    ] %% []
  ) %% []

let intquotient_typing () =
  quant Forall
  [ "x" ; "y" ] [ t_idv ; t_idv ]
  ( appb B.Implies
    [ List (And,
      [ apps T.Mem
        [ Ix 2 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; apps T.IntLteq
          (* This axiom is only used when noarith = true *)
        [ apps (T.IntLit 0) [] %% []
        ; Ix 1 %% []
        ] %% []
      ]) %% []
    ; apps T.Mem
      [ apps T.IntQuotient
        [ Ix 2 %% []
        ; Ix 1 %% []
        ] %% []
      ; apps T.IntSet [] %% []
      ] %% []
    ] %% []
  ) %% []

let intremainder_typing () =
  quant Forall
  [ "x" ; "y" ] [ t_idv ; t_idv ]
  ( appb B.Implies
    [ List (And,
      [ apps T.Mem
        [ Ix 2 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; apps T.IntLteq
          (* This axiom is only used when noarith = true *)
        [ apps (T.IntLit 0) [] %% []
        ; Ix 1 %% []
        ] %% []
      ]) %% []
    ; apps T.Mem
      [ apps T.IntRemainder
        [ Ix 2 %% []
        ; Ix 1 %% []
        ] %% []
      ; apps T.IntRange
        [ apps (T.IntLit 0) [] %% []
        ; apps T.IntMinus
          [ Ix 1 %% []
          ; apps (T.IntLit 1) [] %% []
          ] %% []
        ] %% []
      ] %% []
    ] %% []
  ) %% []

let natplus_typing () =
  quant Forall
  [ "x" ; "y" ] [ t_idv ; t_idv ]
  ( appb B.Implies
    [ appb B.Conj
      [ apps T.Mem
        [ Ix 2 %% []
        ; apps T.NatSet [] %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; apps T.NatSet [] %% []
        ] %% []
      ] %% []
    ; apps T.Mem
      [ apps T.IntPlus
        [ Ix 2 %% []
        ; Ix 1 %% []
        ] %% []
      ; apps T.NatSet [] %% []
      ] %% []
    ] %% []
  ) %% []

let nattimes_typing () =
  quant Forall
  [ "x" ; "y" ] [ t_idv ; t_idv ]
  ( appb B.Implies
    [ appb B.Conj
      [ apps T.Mem
        [ Ix 2 %% []
        ; apps T.NatSet [] %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; apps T.NatSet [] %% []
        ] %% []
      ] %% []
    ; apps T.Mem
      [ apps T.IntTimes
        [ Ix 2 %% []
        ; Ix 1 %% []
        ] %% []
      ; apps T.NatSet [] %% []
      ] %% []
    ] %% []
  ) %% []

let lteq_reflexive () =
  quant Forall
  [ "x" ] [ t_idv ]
  ( appb B.Implies
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps T.IntSet [] %% []
      ] %% []
    ; apps T.IntLteq
      [ Ix 1 %% []
      ; Ix 1 %% []
      ] %% []
    ] %% []
  ) %% []

let lteq_transitive () =
  quant Forall
  [ "x" ; "y" ; "z" ] [ t_idv ; t_idv ; t_idv ]
  ( appb B.Implies
    [ List (And,
      [ apps T.Mem
        [ Ix 3 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; apps T.Mem
        [ Ix 2 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; apps T.IntLteq
        [ Ix 3 %% []
        ; Ix 2 %% []
        ] %% []
      ; apps T.IntLteq
        [ Ix 2 %% []
        ; Ix 1 %% []
        ] %% []
      ]) %% []
    ; apps T.IntLteq
      [ Ix 3 %% []
      ; Ix 1 %% []
      ] %% []
    ] %% []
  ) %% []

let lteq_antisym () =
  quant Forall
  [ "x" ; "y" ] [ t_idv ; t_idv ]
  ( appb B.Implies
    [ List (And,
      [ apps T.Mem
        [ Ix 2 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; apps T.Mem
        [ Ix 1 %% []
        ; apps T.IntSet [] %% []
        ] %% []
      ; apps T.IntLteq
        [ Ix 2 %% []
        ; Ix 1 %% []
        ] %% []
      ; apps T.IntLteq
        [ Ix 1 %% []
        ; Ix 2 %% []
        ] %% []
      ]) %% []
    ; appb ~tys:[ t_idv ] B.Eq
      [ Ix 2 %% []
      ; Ix 1 %% []
      ] %% []
    ] %% []
  ) %% []


(* {4 Tuples} *)

let tuple_isafcn n =
  if n = 0 then
    apps T.FunIsafcn
    [ apps (T.Tuple 0) [] %% []
    ] %% []
  else
    quant Forall
    (gen "x" n) (dupl t_idv n)
    ( apps T.FunIsafcn
      [ apps (T.Tuple n)
        (ixi n) %% []
      ] %% []
    ) %% []

let tupdom_def ~noarith ~t0p n =
  quant Forall
  (gen "x" n) (dupl t_idv n)
  ~pats:[ [
    apps T.FunDom
    [ apps (T.Tuple n)
      (ixi n) %% []
    ] %% []
  ] ]
  ( appb ~tys:[ t_idv ] B.Eq
    [ apps T.FunDom
      [ apps (T.Tuple n)
        (ixi n) %% []
      ] %% []
    ; begin
      if t0p then
        apps T.TIntRange
        [ apps (T.TIntLit 1) [] %% []
        ; apps (T.TIntLit n) [] %% []
        ] %% []
      else
        apps T.IntRange
        [ begin
          if noarith then
            apps (T.IntLit 1) [] %% []
          else
            apps (T.Cast t_int)
            [ apps (T.TIntLit 1) [] %% []
            ] %% []
          end
        ; begin
          if noarith then
            apps (T.IntLit n) [] %% []
          else
            apps (T.Cast t_int)
            [ apps (T.TIntLit n) [] %% []
            ] %% []
          end
        ] %% []
      end
    ] %% []
  ) %% []

let tupapp_def ~noarith n i =
  quant Forall
  (gen "x" n) (dupl t_idv n)
  ~pats:[ [
    apps T.FunApp
    [ apps (T.Tuple n)
      (ixi n) %% []
    ; begin
      if noarith then
        apps (T.IntLit i) [] %% []
      else
        apps (T.Cast t_int)
        [ apps (T.TIntLit i) [] %% []
        ] %% []
      end
    ] %% []
  ] ]
  ( appb ~tys:[ t_idv ] B.Eq
    [ apps T.FunApp
      [ apps (T.Tuple n)
        (ixi n) %% []
      ; begin
        if noarith then
          apps (T.IntLit i) [] %% []
        else
          apps (T.Cast t_int)
          [ apps (T.TIntLit i) [] %% []
          ] %% []
        end
      ] %% []
    ; Ix (n - i + 1) %% []
    ] %% []
  ) %% []

let productset_def n =
  quant Forall
  (gen "s" n @ [ "t" ]) (dupl t_idv (n + 1))
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps (T.Product n)
      (ixi ~shift:1 n) %% []
    ] %% []
  ] ]
  ( appb B.Equiv
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps (T.Product n)
        (ixi ~shift:1 n) %% []
      ] %% []
    ; quant Exists
      (gen "x" n) (dupl t_idv n)
      ( List (And,
        [ appb ~tys:[ t_idv ] B.Eq
          [ Ix (n + 1) %% []
          ; apps (T.Tuple n)
            (ixi n) %% []
          ] %% []
        ] @
        List.init n begin fun i ->
          apps T.Mem
          [ Ix (n - i) %% []
          ; Ix (2*n - i + 1) %% []
          ] %% []
        end) %% []
      ) %% []
    ] %% []
  ) %% []

let productset_intro n =
  quant Forall
  (gen "s" n @ gen "x" n) (dupl t_idv (2 * n))
  ~pats:[ [
    apps (T.Tuple n)
    (ixi n) %% []
  ; apps (T.Product n)
    (ixi ~shift:n n) %% []
  ] ]
  ( appb B.Implies
    [ List (And,
      List.init n begin fun i ->
        apps T.Mem
        [ Ix (n - i) %% []
        ; Ix (2*n - i) %% []
        ] %% []
      end) %% []
    ; apps T.Mem
      [ apps (T.Tuple n)
        (ixi n) %% []
      ; apps (T.Product n)
        (ixi ~shift:n n) %% []
      ] %% []
    ] %% []
  ) %% []

let productset_elim ~noarith n =
  quant Forall
  (gen "s" n @ [ "t" ]) (dupl t_idv (n + 1))
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps (T.Product n)
      (ixi ~shift:1 n) %% []
    ] %% []
  ] ]
  ( appb B.Implies
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps (T.Product n)
        (ixi ~shift:1 n) %% []
      ] %% []
    ; List (And,
      [ appb ~tys:[ t_idv ] B.Eq
        [ Ix 1 %% []
        ; apps (T.Tuple n)
          (List.init n begin fun i ->
            apps T.FunApp
            [ Ix 1 %% []
            ; begin
              if noarith then
                apps (T.IntLit (i + 1)) [] %% []
              else
                apps (T.Cast t_int)
                [ apps (T.TIntLit (i + 1)) [] %% []
                ] %% []
            end
            ] %% []
          end) %% []
        ] %% []
      ] @
      List.init n begin fun i ->
        apps T.Mem
        [ apps T.FunApp
          [ Ix 1 %% []
          ; begin
            if noarith then
              apps (T.IntLit (i + 1)) [] %% []
            else
              apps (T.Cast t_int)
              [ apps (T.TIntLit (i + 1)) [] %% []
              ] %% []
          end
          ] %% []
        ; Ix (n - i + 1) %% []
        ] %% []
      end) %% []
    ] %% []
  ) %% []


(* {4 Records} *)

let record_isafcn fs =
  let n = List.length fs in
  quant Forall
  (gen "x" n) (dupl t_idv n)
  ( apps T.FunIsafcn
    [ apps (T.Rec fs)
      (ixi n) %% []
    ] %% []
  ) %% []

let recdom_def fs =
  let n = List.length fs in
  quant Forall
  (gen "x" n) (dupl t_idv n)
  ~pats:[ [
    apps T.FunDom
    [ apps (T.Rec fs)
      (ixi n) %% []
    ] %% []
  ] ]
  ( appb ~tys:[ t_idv ] B.Eq
    [ apps T.FunDom
      [ apps (T.Rec fs)
        (ixi n) %% []
      ] %% []
    ; apps (T.SetEnum n)
      (List.map begin fun s ->
        apps (T.StrLit s) [] %% []
      end fs) %% []
    ] %% []
  ) %% []

let recapp_def fs =
  let n = List.length fs in
  quant Forall
  (gen "x" n) (dupl t_idv n)
  ( List (And,
    List.mapi begin fun i s ->
      appb ~tys:[ t_idv ] B.Eq
      [ apps T.FunApp
        [ apps (T.Rec fs)
          (ixi n) %% []
        ; apps (T.StrLit s) [] %% []
        ] %% []
      ; Ix (n - i) %% []
      ] %% []
    end fs) %% []
  ) %% []

let recset_def fs =
  let n = List.length fs in
  quant Forall
  (gen "s" n @ [ "r" ]) (dupl t_idv (n+1))
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps (T.RecSet fs)
      (ixi ~shift:1 n) %% []
    ] %% []
  ] ]
  ( appb B.Equiv
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps (T.RecSet fs)
        (ixi ~shift:1 n) %% []
      ] %% []
    ; quant Exists
      (gen "x" n) (dupl t_idv n)
      ( List (And,
        [ appb ~tys:[ t_idv ] B.Eq
          [ Ix (n + 1) %% []
          ; apps (T.Rec fs)
            (ixi n) %% []
          ] %% []
        ] @
        List.mapi begin fun i s ->
          apps T.Mem
          [ Ix (n - i) %% []
          ; Ix (2*n + 1 - i) %% []
          ] %% []
        end fs) %% []
      ) %% []
    ] %% []
  ) %% []

let recset_intro fs =
  let n = List.length fs in
  quant Forall
  (gen "s" n @ gen "x" n) (dupl t_idv (2*n))
  ~pats:[ [
    apps (T.Rec fs)
    (ixi n) %% []
  ; apps (T.RecSet fs)
    (ixi ~shift:n n) %% []
  ] ]
  ( appb B.Implies
    [ List (And,
      List.mapi begin fun i s ->
        apps T.Mem
        [ Ix (n - i) %% []
        ; Ix (2*n - i) %% []
        ] %% []
      end fs) %% []
    ; apps T.Mem
      [ apps (T.Rec fs)
        (ixi n) %% []
      ; apps (T.RecSet fs)
        (ixi ~shift:n n) %% []
      ] %% []
    ] %% []
  ) %% []

let recset_elim fs =
  let n = List.length fs in
  quant Forall
  (gen "s" n @ [ "r" ]) (dupl t_idv (n+1))
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps (T.RecSet fs)
      (ixi ~shift:1 n) %% []
    ] %% []
  ] ]
  ( appb B.Implies
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps (T.RecSet fs)
        (ixi ~shift:1 n) %% []
      ] %% []
    ; List (And,
      [ appb ~tys:[ t_idv ] B.Eq
        [ Ix 1 %% []
        ; apps (T.Rec fs)
          (List.map begin fun s ->
            apps T.FunApp
            [ Ix 1 %% []
            ; apps (T.StrLit s) [] %% []
            ] %% []
          end fs) %% []
        ] %% []
      ] @
      List.mapi begin fun i s ->
        apps T.Mem
        [ apps T.FunApp
          [ Ix 1 %% []
          ; apps (T.StrLit s) [] %% []
          ] %% []
        ; Ix (n + 1 - i) %% []
        ] %% []
      end fs) %% []
    ] %% []
  ) %% []


(* {4 Sequences} *)

let tail_isseq () =
  quant Forall
  [ "s" ; "seq" ] [ t_idv ; t_idv ]
  ( appb B.Implies
    [ apps T.Mem
      [ Ix 1 %% []
      ; apps T.SeqSeq
        [ Ix 2 %% []
        ] %% []
      ] %% []
    ; apps T.Mem
      [ apps T.SeqTail
        [ Ix 1 %% []
        ] %% []
      ; apps T.SeqSeq
        [ Ix 2 %% []
        ] %% []
      ] %% []
    ] %% []
  ) %% []


(* {3 Typed Variants} *)

(* {4 Strings} *)

let t_strset_def () =
  quant Forall
  [ "s" ] [ t_str ]
  ~pats:[ [
    apps (T.TMem t_str)
    [ Ix 1 %% []
    ; apps T.TStrSet [] %% []
    ] %% []
  ] ]
  ( apps (T.TMem t_str)
    [ Ix 1 %% []
    ; apps T.TStrSet [] %% []
    ] %% []
  ) %% []

let t_strlit_distinct s1 s2 =
  appb ~tys:[ t_str ] B.Neq
  [ apps (T.TStrLit s1) [] %% []
  ; apps (T.TStrLit s2) [] %% []
  ] %% []


(* {4 Arithmetic} *)

let t_intset_def ~t0p =
  let cast_if_t0p = fun e ->
    if t0p then
      apps (T.Cast t_int) [ e ] %% []
    else e
  in
  let mem_op =
    if t0p then T.Mem
    else (T.TMem t_int)
  in
  quant Forall
  [ "n" ] [ t_int ]
  ~pats:[ [
    apps mem_op
    [ Ix 1 %% [] |> cast_if_t0p
    ; apps T.TIntSet [] %% []
    ] %% []
  ] ]
  ( apps mem_op
    [ Ix 1 %% [] |> cast_if_t0p
    ; apps T.TIntSet [] %% []
    ] %% []
  ) %% []

let t_natset_def ~t0p =
  let cast_if_t0p = fun e ->
    if t0p then
      apps (T.Cast t_int) [ e ] %% []
    else e
  in
  let mem_op =
    if t0p then T.Mem
    else (T.TMem t_int)
  in
  quant Forall
  [ "n" ] [ t_int ]
  ~pats:[ [
    apps mem_op
    [ Ix 1 %% [] |> cast_if_t0p
    ; apps T.TNatSet [] %% []
    ] %% []
  ] ]
  ( appb B.Equiv
    [ apps mem_op
      [ Ix 1 %% [] |> cast_if_t0p
      ; apps T.TNatSet [] %% []
      ] %% []
    ; apps T.TIntLteq
      [ apps (T.TIntLit 0) [] %% []
      ; Ix 1 %% []
      ] %% []
    ] %% []
  ) %% []

let t_intrange_def ~t0p =
  let cast_if_t0p = fun e ->
    if t0p then
      apps (T.Cast t_int) [ e ] %% []
    else e
  in
  let mem_op =
    if t0p then T.Mem
    else (T.TMem t_int)
  in
  quant Forall
  [ "m" ; "n" ; "p" ] [ t_int ; t_int ; t_int ]
  ~pats:[ [
    apps mem_op
    [ Ix 1 %% [] |> cast_if_t0p
    ; apps T.TIntRange
      [ Ix 3 %% []
      ; Ix 2 %% []
      ] %% []
    ] %% []
  ] ]
  ( appb B.Equiv
    [ apps mem_op
      [ Ix 1 %% [] |> cast_if_t0p
      ; apps T.TIntRange
        [ Ix 3 %% []
        ; Ix 2 %% []
        ] %% []
      ] %% []
    ; appb B.Conj
      [ apps T.TIntLteq
        [ Ix 3 %% []
        ; Ix 1 %% []
        ] %% []
      ; apps T.TIntLteq
        [ Ix 1 %% []
        ; Ix 2 %% []
        ] %% []
      ] %% []
    ] %% []
  ) %% []


(* {3 Get Axiom} *)

(* These annotations are used to rewrite instances of an axiom schema.
 * See {!N_flatten}. *)
let mark tla_smb e =
  let smb = mk_smb tla_smb in
  assign e smb_prop smb

let get_axm ~solver tla_smb =
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
  match tla_smb with
  | T.ChooseDef -> choose_def () |> mark T.Choose
  | T.ChooseExt -> choose_ext ()
  | T.SetExt -> set_ext ()
  | T.SubsetEqDef -> subseteq_def ()
  | T.SubsetEqIntro -> subseteq_intro ()
  | T.SubsetEqElim -> subseteq_elim ()
  | T.EnumDef n -> setenum_def n
  | T.EnumDefIntro n -> setenum_intro n
  | T.EnumDefElim n -> setenum_elim n
  | T.UnionDef -> union_def ()
  | T.UnionIntro -> union_intro ()
  | T.UnionElim -> union_elim ()
  | T.SubsetDef -> subset_def ()
  | T.SubsetIntro -> subset_intro ()
  | T.SubsetElim -> subset_elim ()
  | T.CupDef -> cup_def ()
  | T.CapDef -> cap_def ()
  | T.SetMinusDef -> setminus_def ()
  | T.SetStDef -> setst_def () |> mark T.SetSt
  | T.SetOfDef n -> setof_def n |> mark (T.SetOf n)
  | T.SetOfIntro n -> setof_intro n |> mark (T.SetOf n)
  | T.SetOfElim n -> setof_elim n |> mark (T.SetOf n)
  | T.StrLitIsstr s -> strlit_isstr s
  | T.StrLitDistinct (s1, s2) -> strlit_distinct s1 s2
  | T.IntLitIsint n -> intlit_isint n
  | T.IntLitDistinct (m, n) -> intlit_distinct m n
  | T.IntLitZeroCmp n -> intlit_zerocmp n
  | T.NatSetDef -> natset_def ~noarith
  | T.IntPlusTyping -> intplus_typing ()
  | T.IntUminusTyping -> intuminus_typing ()
  | T.IntMinusTyping -> intminus_typing ()
  | T.IntTimesTyping -> inttimes_typing ()
  | T.IntQuotientTyping -> intquotient_typing ()
  | T.IntRemainderTyping -> intremainder_typing ()
  | T.IntExpTyping -> intexp_typing ()
  | T.NatPlusTyping -> natplus_typing ()
  | T.NatTimesTyping -> nattimes_typing ()
  | T.IntRangeDef -> intrange_def ()
  | T.LteqReflexive -> lteq_reflexive ()
  | T.LteqTransitive -> lteq_transitive ()
  | T.LteqAntisym -> lteq_antisym ()
  | T.FunExt -> fcn_ext ()
  | T.FunConstrIsafcn -> fcnconstr_isafcn () |> mark T.FunConstr
  | T.FunSetDef -> fcnset_def ()
  | T.FunSetIntro -> fcnset_intro ()
  | T.FunSetElim1 -> fcnset_elim1 ()
  | T.FunSetElim2 -> fcnset_elim2 ()
  | T.FunDomDef -> fcndom_def () |> mark T.FunConstr
  | T.FunAppDef -> fcnapp_def () |> mark T.FunConstr
  | T.FunExceptIsafcn -> fcnexcept_isafcn ()
  | T.FunExceptDomDef -> fcnexceptdom_def ()
  | T.FunExceptAppDef -> fcnexceptapp_def ()
  | T.TupIsafcn n -> tuple_isafcn n
  | T.TupDomDef n -> tupdom_def ~noarith ~t0p n
  | T.TupAppDef (n, i) -> tupapp_def ~noarith n i
  | T.ProductDef n -> productset_def n
  | T.ProductIntro n -> productset_intro n
  | T.ProductElim n -> productset_elim ~noarith n
  | T.RecIsafcn fs -> record_isafcn fs
  | T.RecDomDef fs -> recdom_def fs
  | T.RecAppDef fs -> recapp_def fs
  | T.RecSetDef fs -> recset_def fs
  | T.RecSetIntro fs -> recset_intro fs
  | T.RecSetElim fs -> recset_elim fs
  | T.SeqTailIsSeq -> tail_isseq ()

  | T.TStrSetDef -> t_strset_def ()
  | T.TStrLitDistinct (s1, s2) -> t_strlit_distinct s1 s2
  | T.TIntSetDef -> t_intset_def ~t0p
  | T.TNatSetDef -> t_natset_def ~t0p
  | T.TIntRangeDef -> t_intrange_def ~t0p

  | T.CastInj ty0 -> cast_inj ty0
  | T.TypeGuard ty0 -> type_guard ty0
  | T.Typing tla_smb -> op_typing tla_smb

