(* Copyright (C) 2011-2014  INRIA and Microsoft Corporation *)
open Expr.T

type t = hyp Deque.dq * int Ctx.ctx

val dot : t
val length : t -> int
val bump : t -> t
val to_fresh : bounds -> hyp list
val adj : t -> hyp -> t * (string * hyp)
val adjs : t -> hyp list -> t * (string * hyp) list
val adj_bs : t -> bounds -> t * (string * Axioms.smtsort) list * hyp list
val is_bounded : hyp Deque.dq -> int -> bool
val tla_id : t -> int -> string
val smt_id : t -> int -> string
val from_hyps : t -> hyp Deque.dq -> t
