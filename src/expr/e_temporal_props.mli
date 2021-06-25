(*
 * functions for checking temporal properties
 * Copyright (C) 2013  INRIA and Microsoft Corporation
 *)

val box_closure : E_t.hyp Deque.dq -> E_t.expr -> bool
val diamond_closure : E_t.hyp Deque.dq -> E_t.expr -> bool
val compute_time : E_t.hyp Deque.dq -> E_t.expr -> E_t.time
val check_time_change : E_t.hyp Deque.dq -> E_t.time -> E_t.time
