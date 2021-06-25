(*
 * mod/standard --- standard modules
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Standard modules *)

open M_t


(** all TLAPM builtin operators, including TLA+ builtins *)
val tlapm       : mule
(** natural numbers *)
val naturals    : mule
(** integers *)
val integers    : mule
(** reals *)
val reals       : mule
(** sequences *)
val sequences   : mule
(** TLC *)
val tlc         : mule
(** the initial module context, constructed at startup *)
val initctx  : modctx
