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
  let xs =
    List.map2 begin fun x ty0 ->
      (assign (x %% []) Props.ty0_prop ty0, Constant, No_domain)
    end xs ty0s
  in
  let e = maybe_assign pattern_prop e pats in
  Quant (q, xs, e)

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
  if ty0 = t_bol then
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
  else
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
  let dat = N_data.get_data t_smb in
  let i_smb = Option.get (dat.dat_tver) in
  let ty2 = dat.dat_ty2 in
  let Ty1 (ty0s, ty0) =
    try downcast_ty1 ty2
    with _ -> error "Not implemented" (* TODO *)
  in
  let n = List.length ty0s in
  quant Forall
  (gen "x" n) ty0s
  ~pats:[ [
    apps i_smb
    (List.map2 begin fun e ty0 ->
      apps (T.Cast ty0) [ e ] %% []
    end (ixi n) ty0s) %% []
  ] ]
  ( appb ~tys:[ t_idv ] B.Eq
    [ apps i_smb
      (List.map2 begin fun e ty0 ->
        apps (T.Cast ty0) [ e ] %% []
      end (ixi n) ty0s) %% []
    ; apps (T.Cast ty0)
      [ apps t_smb
        (ixi n) %% []
      ] %% []
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

let setenum_def n =
  quant Forall
  (gen "a" n @ [ "x" ]) (dupl t_idv (n+1))
  ~pats:[ [
    apps T.Mem
    [ Ix 1 %% []
    ; apps (T.SetEnum n) [] %% []
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


(* {4 Functions} *)

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

let fcndom_def () =
  seq
  [ "F" ] [ Ty1 ([ t_idv ], t_idv) ]
  ( quant Forall
    [ "a" ] [ t_idv ]
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

let natset_def () =
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
        [ apps (T.IntLit 0) [] %% []
        ; Ix 1 %% []
        ] %% []
      ] %% []
    ] %% []
  ) %% []

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

let intrange_def () =
  quant Forall
  [ "a" ; "b" ] [ t_idv ; t_idv ]
  ~pats:[ [
    apps T.Mem
    [ Ix 2 %% []
    ; apps T.IntSet [] %% []
    ] %% []
  ; apps T.Mem
    [ Ix 1 %% []
    ; apps T.IntSet [] %% []
    ] %% []
  ] ]
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
    ; quant Forall
      [ "x" ] [ t_idv ]
      ~pats:[ [
        apps T.Mem
        [ Ix 1 %% []
        ; apps T.IntRange
          [ Ix 3 %% []
          ; Ix 2 %% []
          ] %% []
        ] %% []
      ] ]
      ( appb B.Equiv
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
      ) %% []
    ] %% []
  ) %% []


(* {4 Tuples} *)

let tuple_isafcn n =
  quant Forall
  (gen "x" n) (dupl t_idv n)
  ( apps T.FunIsafcn
    [ apps (T.Tuple n)
      (ixi n) %% []
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
    ; List (And,
      [ apps T.FunIsafcn
        [ Ix 1 %% []
        ] %% []
      ; appb ~tys:[ t_idv ] B.Eq
        [ apps T.FunDom
          [ Ix 1 %% []
          ] %% []
        ; apps T.IntRange
          [ apps (T.IntLit 1) [] %% []
          ; apps (T.IntLit n) [] %% []
          ] %% []
        ] %% []
      ] @
      List.init n begin fun i ->
        apps T.Mem
        [ apps T.FunApp
          [ Ix 1 %% []
          ; apps (T.IntLit (i + 1)) [] %% []
          ] %% []
        ; Ix (n - i + 1) %% []
        ] %% []
      end) %% []
    ] %% []
  ) %% []

let productset_def_alt n =
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

let tupdom_def n =
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
    ; apps T.IntRange
      [ apps (T.IntLit 1) [] %% []
      ; apps (T.IntLit n) [] %% []
      ] %% []
    ] %% []
  ) %% []

let tupapp_def n i =
  quant Forall
  (gen "x" n) (dupl t_idv n)
  ~pats:[ [
    apps T.FunApp
    [ apps (T.Tuple n)
      (ixi n) %% []
    ; apps (T.IntLit i) [] %% []
    ] %% []
  ] ]
  ( appb ~tys:[ t_idv ] B.Eq
    [ apps T.FunApp
      [ apps (T.Tuple n)
        (ixi n) %% []
      ; apps (T.IntLit i) [] %% []
      ] %% []
    ; Ix (n - i + 1) %% []
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
    ; List (And,
      [ apps T.FunIsafcn
        [ Ix 1 %% []
        ] %% []
      ; appb ~tys:[ t_idv ] B.Eq
        [ apps T.FunDom
          [ Ix 1 %% []
          ] %% []
        ; apps (T.SetEnum n)
          (List.map begin fun s ->
            apps (T.StrLit s) [] %% []
          end fs) %% []
        ] %% []
      ] @
      List.mapi begin fun i s ->
        apps T.Mem
        [ apps T.FunApp
          [ Ix 1 %% []
          ; apps (T.StrLit s) [] %% []
          ] %% []
        ; Ix (n - i + 1) %% []
        ] %% []
      end fs) %% []
    ] %% []
  ) %% []

let recset_def_alt fs =
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


(* {3 Typed Variants} *)

(* {4 Strings} *)

let t_strlit_distinct s1 s2 =
  appb ~tys:[ t_str ] B.Neq
  [ apps (T.TStrLit s1) [] %% []
  ; apps (T.TStrLit s2) [] %% []
  ] %% []


(* {3 Get Axiom} *)

let get_axm = function
  | T.ChooseDef -> choose_def ()
  | T.ChooseExt -> choose_ext ()
  | T.SetExt -> set_ext ()
  | T.SubsetEqDef -> subseteq_def ()
  | T.EnumDef n -> setenum_def n
  | T.UnionDef -> union_def ()
  | T.SubsetDef -> subset_def ()
  | T.CupDef -> cup_def ()
  | T.CapDef -> cap_def ()
  | T.SetMinusDef -> setminus_def ()
  | T.SetStDef -> setst_def ()
  | T.SetOfDef n -> setof_def n
  | T.StrLitIsstr s -> strlit_isstr s
  | T.StrLitDistinct (s1, s2) -> strlit_distinct s1 s2
  | T.IntLitIsint n -> intlit_isint n
  | T.IntLitDistinct (m, n) -> intlit_distinct m n
  | T.NatSetDef -> natset_def ()
  | T.IntPlusTyping -> intplus_typing ()
  | T.IntUminusTyping -> intuminus_typing ()
  | T.IntMinusTyping -> intminus_typing ()
  | T.IntTimesTyping -> inttimes_typing ()
  | T.IntQuotientTyping -> intquotient_typing ()
  | T.IntRemainderTyping -> intremainder_typing ()
  | T.IntExpTyping -> intexp_typing ()
  | T.IntRangeDef -> intrange_def ()
  | T.FunExt -> fcn_ext ()
  | T.FunConstrIsafcn -> fcnconstr_isafcn ()
  | T.FunSetDef -> fcnset_def ()
  | T.FunDomDef -> fcndom_def ()
  | T.FunAppDef -> fcnapp_def ()
  | T.TStrLitDistinct (s1, s2) -> t_strlit_distinct s1 s2
  | T.TupIsafcn n -> tuple_isafcn n
  | T.ProductDef n -> productset_def_alt n
  | T.TupDomDef n -> tupdom_def n
  | T.TupAppDef (n, i) -> tupapp_def n i
  | T.RecIsafcn fs -> record_isafcn fs
  | T.RecSetDef fs -> recset_def_alt fs
  | T.RecDomDef fs -> recdom_def fs
  | T.RecAppDef fs -> recapp_def fs
  | T.CastInj ty0 -> cast_inj ty0
  | T.TypeGuard ty0 -> type_guard ty0
  | T.Typing tla_smb -> op_typing tla_smb


(* FIXME adapt *)
  (*

(* {3 Schema Instance} *)

let inst_choose ty m p =
  let sub = Expr.Subst.shift 1 in (* skip x *)
  all (gen "c" m @ [ "x" ]) ?tys:(Option.map (fun (ty, tys) -> tys @ [ ty ]) ty) ~pats:[ [
    app (Expr.Subst.app_expr sub p) [ Ix 1 %% [] ] %% []
    |> Expr.Subst.app_expr (Expr.Subst.shift 0) (* force normalize *)
  ] ] (
    ifx B.Implies (
      app (Expr.Subst.app_expr sub p) [ Ix 1 %% [] ] %% []
      |> Expr.Subst.app_expr (Expr.Subst.shift 0) (* force normalize *)
    ) (
      app (Expr.Subst.app_expr sub p) [
        app (Ix 0 %% []) (ixi ~shift:1 m) %% []
      ] %% []
      |> Expr.Subst.app_expr (Expr.Subst.shift 0) (* force normalize *)
    ) %% []
  ) %% []

let inst_setst ty m p =
  all ([ "a" ] @ gen "c" m @ [ "x" ])
  ?tys:(Option.map (fun (ty, tys) -> [ TSet ty ] @ tys @ [ ty ]) ty)
  ~pats:[ [
    ifx ?tys:(Option.map (fun (ty, _) -> [ ty ]) ty)
    B.Mem (
      Ix 1 %% []
    ) (
      app (
        Ix 0 %% []
      ) (ixi ~shift:1 (1 + m)) %% []
    ) %% []
  ] ] (
    ifx B.Equiv (
      ifx ?tys:(Option.map (fun (ty, _) -> [ ty ]) ty)
      B.Mem (
        Ix 1 %% []
      ) (
        app (
          Ix 0 %% []
        ) (ixi ~shift:1 (1 + m)) %% []
      ) %% []
    ) (
      ifx B.Conj (
        ifx ?tys:(Option.map (fun (ty, _) -> [ ty ]) ty)
        B.Mem (
          Ix 1 %% []
        ) (
          Ix (m + 2) %% []
        ) %% []
      ) (
        (* skip x *)
        let sub = Expr.Subst.shift 1 in
        app (Expr.Subst.app_expr sub p) [ Ix 1 %% [] ] %% []
        |> Expr.Subst.app_expr (Expr.Subst.shift 0) (* force normalize *)
      ) %% []
    ) %% []
  ) %% []

let inst_setof n ttys m p =
  let tys, ty, ty2s =
    match ttys with
    | None -> (List.init n (fun _ -> None), None, List.init m (fun _ -> None))
    | Some (tys, ty, ty2s) -> (List.map (fun ty -> Some ty) tys, Some ty, List.map (fun ty -> Some ty) ty2s)
  in
  all (gen "a" n @ gen "c" m @ [ "x" ])
  ?tys:(Option.map (fun (tys, ty, ty2s) -> List.map (fun ty -> TSet ty) tys @ ty2s @ [ ty ]) ttys) ~pats:[ [
    ifx ?tys:(Option.map (fun ty -> [ ty ]) ty)
    B.Mem (
      Ix 1 %% []
    ) (
      app (
        Ix 0 %% []
      ) (ixi ~shift:1 (n + m)) %% []
    ) %% []
  ] ] (
    ifx B.Equiv (
      ifx ?tys:(Option.map (fun ty -> [ ty ]) ty)
      B.Mem (
        Ix 1 %% []
      ) (
        app (
          Ix 0 %% []
        ) (ixi ~shift:1 (n + m)) %% []
      ) %% []
    ) (
      exi (gen "y" n)
      ?tys:(Option.map (fun (x, _, _) -> x) ttys) (
        List (And, List.map2 begin fun e1 (e2, ty) ->
          ifx ?tys:(Option.map (fun ty -> [ ty ]) ty)
          B.Mem e1 e2 %% []
        end (ixi n) (List.combine (ixi ~shift:(n + 1) n) tys)
        @ [
          ifx ?tys:(Option.map (fun ty -> [ ty ]) ty)
          B.Eq (
            Ix (n + 1) %% []
          ) (
            let sub = Expr.Subst.shift (1 + n) in (* skip x and ys *)
            app (Expr.Subst.app_expr sub p) (ixi n) %% []
            |> Expr.Subst.app_expr (Expr.Subst.shift 0) (* force normalize *)
          ) %% []
        ]
        ) %% []
      ) %% []
    ) %% []
  ) %% []

  *)
