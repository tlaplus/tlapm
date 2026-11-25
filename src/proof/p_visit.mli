(* Visitor for proofs.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open Deque
open Expr.T
open Expr.Visit

open P_t


val bump: 's scx -> int -> 's scx

class virtual ['s] map: object
  inherit ['s] Expr.Visit.map
  method proof: 's scx -> proof -> proof
  method steps: 's scx -> step list -> 's scx * step list
  method step: 's scx -> step -> 's scx * step
  method usable: 's scx -> usable -> usable
end

class virtual ['s] iter: object
  inherit ['s] Expr.Visit.iter
  method proof: 's scx -> proof -> unit
  method steps: 's scx -> step list -> 's scx
  method step: 's scx -> step -> 's scx
  method qed: 's scx -> qed_step -> unit
  method usable: 's scx -> usable -> unit
end

class virtual ['s] map_concrete: object
    inherit ['s] map
    inherit ['s] Expr.Visit.map_concrete
end

class virtual ['s] iter_concrete: object
    inherit ['s] iter
    inherit ['s] Expr.Visit.iter_concrete
end
