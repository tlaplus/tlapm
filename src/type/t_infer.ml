(*
 * type/infer.ml --- main procedure
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T

let infer sq =
  Typ_system.type_construct sq

