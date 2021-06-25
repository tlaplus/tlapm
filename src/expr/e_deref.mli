(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

open E_t

val resolve_bang:
    hyp Deque.dq -> expr ->
    expr list -> sel list -> expr
val is_badexp: expr -> bool
val badexp: expr
