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

module B = Builtin


(* {3 Helpers} *)

let annot h ty = assign h Props.type_prop ty
let targs a tys = assign a Props.targs_prop tys

let app ?tys op es =
  let op =
    match tys with
    | None -> op
    | Some tys -> targs op tys
  in
  match es with
  | [] -> Apply (op, []) (* previously just op, but loss of properties *)
  | _ -> Apply (op, es)

let appb ?tys b es =
  app ?tys (Internal b %% []) es

let una ?tys b e1    = appb ?tys b [ e1 ]
let ifx ?tys b e1 e2 = appb ?tys b [ e1 ; e2 ]

let quant q xs ?tys e =
  match tys with
  | None ->
      Quant (q, List.map (fun x -> (x %% [], Constant, No_domain)) xs, e)
  | Some tys ->
      Quant (q, List.map2 (fun x ty -> (annot (x %% []) ty, Constant, No_domain)) xs tys, e)

let all xs ?tys e = quant Forall xs ?tys e
let exi xs ?tys e = quant Exists xs ?tys e

let dupl a n = List.init n (fun _ -> a)

let gen x n = List.init n (fun i -> x ^ string_of_int (i + 1))
(** [gen "x" n] = [ "x1" ; .. ; "xn" ] *)

let ixi ?(shift=0) n = List.init n (fun i -> Ix (shift + n - i) %% [])
(** [ixi n]          = [ Ix n ; .. ; Ix 2 ; Ix 1 ]
    [ixi ~shift:s n] = [ Ix (s+n) ; .. ; Ix (s+2) ; Ix (s+1) ]
*)

let fresh x ?its ty =
  let targ, shp =
    match its with
    | None -> TRg ty, Shape_expr
    | Some its -> TOp (its, ty), Shape_op (List.length its)
  in
  let h = assign (x %% []) Props.targ_prop targ in
  Fresh (h, shp, Constant, Unbounded)


(* {3 Logic} *)

let choose ty =
  Sequent {
    context = [
      fresh "P" ~its:[ ty ] (TAtom TBool) %% []
    ] |> Deque.of_list ;
    active =
      all [ "x" ] ~tys:[ ty ] (
        ifx B.Implies (
          app (Ix 2 %% []) [ Ix 1 %% [] ] %% []
        ) (
          app (Ix 2 %% []) [
            Choose (annot ("y" %% []) ty, None,
            app (Ix 3 %% []) [ Ix 1 %% [] ] %% []) %% []
          ] %% []
        ) %% []
      ) %% []
  } %% []


(* {3 Sets} *)

let subseteq ty =
  all [ "x" ; "y" ] ~tys:[ TSet ty ; TSet ty ] (
    ifx B.Equiv (
      ifx B.Subseteq (Ix 2 %% []) (Ix 1 %% []) %% []
    ) (
      all [ "z" ] ~tys:[ ty ] (
        ifx B.Implies (
          ifx ~tys:[ ty ] B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
        ) (
          ifx ~tys:[ ty ] B.Mem (Ix 1 %% []) (Ix 2 %% []) %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

let setenum n ty =
  if n = 0 then
    all [ "x" ] ~tys:[ ty ] (
      una B.Neg (
        ifx ~tys:[ ty ] B.Mem (
          Ix 1 %% []
        ) (
          app (SetEnum [] %% []) ~tys:[ ty ] [] %% []
        ) %% []
      ) %% []
    ) %% []
  else
    all (gen "a" n @ [ "x" ]) ~tys:(dupl ty (n + 1)) (
      ifx B.Equiv (
        ifx ~tys:[ ty ] B.Mem (
          Ix 1 %% []
        ) (
          app ~tys:[ ty ] (SetEnum (ixi ~shift:1 n) %% []) [] %% []
        ) %% []
      ) (
        List (Or, List.map begin fun e ->
          ifx ~tys:[ ty ] B.Eq (Ix 1 %% []) e %% []
        end (ixi ~shift:1 n)) %% []
      ) %% []
    ) %% []

let union ty =
  all [ "a" ; "x" ] ~tys:[ TSet (TSet ty) ; ty ] (
    ifx B.Equiv (
      ifx ~tys:[ ty ] B.Mem (
        Ix 1 %% []
      ) (
        una ~tys:[ ty ] B.UNION (
          Ix 2 %% []
        ) %% []
      ) %% []
    ) (
      exi [ "y" ] ~tys:[ TSet ty ] (
        ifx B.Conj (
          ifx ~tys:[ TSet ty ] B.Mem (
            Ix 1 %% []
          ) (
            Ix 3 %% []
          ) %% []
        ) (
          ifx ~tys:[ ty ] B.Mem (
            Ix 2 %% []
          ) (
            Ix 1 %% []
          ) %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

let subset ty =
  all [ "a" ; "x" ] ~tys:[ TSet ty ; TSet ty ] (
    ifx B.Equiv (
      ifx ~tys:[ ty ] B.Mem (
        Ix 1 %% []
      ) (
        una ~tys:[ ty ] B.SUBSET (
          Ix 2 %% []
        ) %% []
      ) %% []
    ) (
      all [ "y" ] ~tys:[ ty ] (
        ifx B.Implies (
          ifx ~tys:[ ty ] B.Mem (
            Ix 1 %% []
          ) (
            Ix 2 %% []
          ) %% []
        ) (
          ifx ~tys:[ ty ] B.Mem (
            Ix 1 %% []
          ) (
            Ix 3 %% []
          ) %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

let cup ty =
  all [ "a" ; "b" ; "x" ] ~tys:[ TSet ty ; TSet ty ; ty ] (
    ifx B.Equiv (
      ifx ~tys:[ ty ] B.Mem (
        Ix 1 %% []
      ) (
        ifx ~tys:[ ty ] B.Cup (
          Ix 3 %% []
        ) (
          Ix 2 %% []
        ) %% []
      ) %% []
    ) (
      ifx B.Disj (
        ifx ~tys:[ ty ] B.Mem (
          Ix 1 %% []
        ) (
          Ix 3 %% []
        ) %% []
      ) (
        ifx ~tys:[ ty ] B.Mem (
          Ix 1 %% []
        ) (
          Ix 2 %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

let cap ty =
  all [ "a" ; "b" ; "x" ] ~tys:[ TSet ty ; TSet ty ; ty ] (
    ifx B.Equiv (
      ifx ~tys:[ ty ] B.Mem (
        Ix 1 %% []
      ) (
        ifx ~tys:[ ty ] B.Cap (
          Ix 3 %% []
        ) (
          Ix 2 %% []
        ) %% []
      ) %% []
    ) (
      ifx B.Conj (
        ifx ~tys:[ ty ] B.Mem (
          Ix 1 %% []
        ) (
          Ix 3 %% []
        ) %% []
      ) (
        ifx ~tys:[ ty ] B.Mem (
          Ix 1 %% []
        ) (
          Ix 2 %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

let setminus ty =
  all [ "a" ; "b" ; "x" ] ~tys:[ TSet ty ; TSet ty ; ty ] (
    ifx B.Equiv (
      ifx ~tys:[ ty ] B.Mem (
        Ix 1 %% []
      ) (
        ifx ~tys:[ ty ] B.Setminus (
          Ix 3 %% []
        ) (
          Ix 2 %% []
        ) %% []
      ) %% []
    ) (
      ifx B.Conj (
        ifx ~tys:[ ty ] B.Mem (
          Ix 1 %% []
        ) (
          Ix 3 %% []
        ) %% []
      ) (
        una ~tys:[ ty ] B.Neg (
          ifx ~tys:[ ty ] B.Mem (
            Ix 1 %% []
          ) (
            Ix 2 %% []
          ) %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []


let setst ty =
  Sequent {
    context = [
      fresh "P" ~its:[ ty ] (TAtom TBool) %% []
    ] |> Deque.of_list ;
    active =
      all [ "a" ; "x" ] ~tys:[ TSet ty ; ty ] (
        ifx B.Equiv (
          ifx ~tys:[ ty ] B.Mem (
            Ix 1 %% []
          ) (
            app ~tys:[ ty ] (
              SetSt (
                annot ("y" %% []) ty,
                Ix 2 %% [],
                app (Ix 4 %% []) [ Ix 1 %% [] ] %% []
              ) %% []
            ) [] %% []
          ) %% []
        ) (
          ifx B.Conj (
            ifx ~tys:[ ty ] B.Mem (
              Ix 1 %% []
            ) (
              Ix 2 %% []
            ) %% []
          ) (
            app (Ix 3 %% []) [ Ix 1 %% [] ] %% []
          ) %% []
        ) %% []
      ) %% []
  } %% []

let setof tys ty =
  Sequent {
    context = [
      fresh "P" ~its:tys ty %% []
    ] |> Deque.of_list ;
    active =
      let n = List.length tys in
      all (gen "a" n @ [ "x" ]) ~tys:(List.map (fun ty -> TSet ty) tys @ [ ty ]) (
        ifx B.Equiv (
          ifx ~tys:[ ty ] B.Mem (
            Ix 1 %% []
          ) (
            app ~tys:[ ty ] (
              SetOf (
                app (Ix (2*n + 2) %% []) (ixi n) %% [],
                List.map2 begin fun e ty ->
                  let h = annot ("y" %% []) ty in
                  (h, Constant, Domain e)
                end (ixi ~shift:1 n) tys
              ) %% []
            ) [] %% []
          ) %% []
        ) (
          exi (gen "y" n) ~tys:tys (
            List (And, List.map2 begin fun e1 (e2, ty) ->
              ifx ~tys:[ ty ] B.Mem e1 e2 %% []
            end (ixi n) (List.combine (ixi ~shift:1 n) tys)
            @ [
              ifx ~tys:[ ty ] B.Eq (
                Ix (n + 1) %% []
              ) (
                app (Ix (2*n + 2) %% []) (ixi n) %% []
              ) %% []
            ]
            ) %% []
          ) %% []
        ) %% []
      ) %% []
  } %% []


(* {3 Functions} *)

let arrow ty1 ty2 =
  Internal B.TRUE %% []

let domain ty1 ty2 =
  Internal B.TRUE %% []

let fcnapp ty1 ty2 =
  Internal B.TRUE %% []

let except ty1 ty2 =
  Internal B.TRUE %% []


(* {3 Booleans} *)

let booleans =
  Internal B.TRUE %% []


(* {3 Strings} *)

let strings =
  Internal B.TRUE %% []


(* {3 Arithmetic} *)

let ints =
  Internal B.TRUE %% []

let nats =
  Internal B.TRUE %% []

let reals =
  Internal B.TRUE %% []

