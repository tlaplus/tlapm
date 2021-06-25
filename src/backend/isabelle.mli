(* Interface to Isabelle.

Copyright (C) 2011  INRIA and Microsoft Corporation
*)

(* backend/zenon.ml *)
type ctx = int Ctx.ctx
val dot: ctx
val bump: ctx -> ctx
val length: ctx -> int
val adj: ctx -> Util.hint -> ctx * string
val adjs:
    ctx -> Util.hint list -> ctx * string list
val cook: string -> string
val lookup_id: ctx -> int -> string
val crypthash: ctx -> Expr.T.expr -> string

(* backend/prep.ml *)
val thy_temp:
    Proof.T.obligation -> string ->
    string -> out_channel -> unit
(** [thy_temp obligation tactic
isabelle_module_name out_file]
*)

(* backend/server.ml *)
val thy_init: string -> string -> out_channel
val thy_write:
    out_channel -> Proof.T.obligation -> string -> unit
val thy_close: string -> out_channel -> unit

(* tlapm.ml *)
val recheck: string * int * string -> unit
