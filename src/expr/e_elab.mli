(*
 * expr/elab.ml --- elaborate expressions
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Expression elaborater *)

open Deque
open E_t


val desugar : expr -> expr
  (* moved to action frontend *)
(* val prime_normalize : hyp Deque.dq -> expr -> expr *)
val normalize : hyp Deque.dq -> expr -> expr

val replace_at : unit E_visit.scx -> expr -> expr -> expr
val get_at : expr -> expr
