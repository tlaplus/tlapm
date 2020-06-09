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

let app b es = Apply (Internal b %% [], es)

let una b e1    = app b [ e1 ]
let ifx b e1 e2 = app b [ e1 ; e2 ]

let quant q xs e = Quant (q, List.map (fun x -> (x %% [], Constant, No_domain)) xs, e)
let all xs e = quant Forall xs e
let exi xs e = quant Exists xs e

let gen x n = List.init n (fun i -> x ^ string_of_int (i + 1))
(** [gen "x" n] = [ "x1" ; .. ; "xn" ] *)

let ixi ?(shift=0) n = List.init n (fun i -> Ix (shift + n - i) %% [])
(** [ixi n]          = [ Ix n ; .. ; Ix 2 ; Ix 1 ]
    [ixi ~shift:s n] = [ Ix (s+n) ; .. ; Ix (s+2) ; Ix (s+1) ]
*)



(* {3 Logic} *)

let choose ty =
  Internal B.TRUE %% []


(* {3 Sets} *)

let subseteq ty =
  Internal B.TRUE %% []

let setenum n ty =
  Internal B.TRUE %% []

let union ty =
  Internal B.TRUE %% []

let subset ty =
  Internal B.TRUE %% []

let cup ty =
  Internal B.TRUE %% []

let cap ty =
  Internal B.TRUE %% []

let setminus ty =
  Internal B.TRUE %% []

let setst ty =
  Internal B.TRUE %% []

let setof tys ty =
  Internal B.TRUE %% []


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

