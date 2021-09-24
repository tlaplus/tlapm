(*
 * proof/visit.ml --- default visitor for proofs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** default visitors for proofs *)

open Deque

open Expr.T
open P_t
open Expr.Visit

val bump : 's scx -> int -> 's scx

class virtual ['s] map : object
  inherit ['s] Expr.Visit.map
  method proof  : 's scx -> proof -> proof
  method steps  : 's scx -> step list -> 's scx * step list
  method step   : 's scx -> step -> 's scx * step
  method usable : 's scx -> usable -> usable
end

class virtual ['s] iter : object
  inherit ['s] Expr.Visit.iter
  method proof  : 's scx -> proof -> unit
  method steps  : 's scx -> step list -> 's scx
  method step   : 's scx -> step -> 's scx
  method usable : 's scx -> usable -> unit
end

class virtual ['s] json_map: object
    inherit ['s] Expr.Visit.json_map
    method proof:
        's scx -> proof -> string
    method steps:
        's scx -> step list ->
            's scx * string
    method step:
        's scx -> step ->
            's scx * string
    method usable:
        's scx -> usable -> string
end
