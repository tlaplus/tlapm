(*
 * type/simple.ml --- simple type reconstruction
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T

open T_t


(* {3 Context} *)

type ty_t =
  | Rg of ty
  | Sch of ty_sch

type ctx = ty_t Ctx.t


(* {3 Helpers} *)

let error ?at mssg =
  Errors.bug ?at mssg


(* {3 Main} *)

let main sq = sq

