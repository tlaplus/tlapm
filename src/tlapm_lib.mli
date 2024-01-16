(*
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

module Module = Module
module Property = Property
module Proof = Proof
module Expr = Expr
module Util = Util
module Loc = Loc
module Ctx = Ctx
module Backend = Backend

val main : string list -> unit
val init : unit -> unit

val module_of_string : string -> string -> (Module.T.mule, (string option* string)) result
(** Parse module from a specified string, assume it is located in the specified path. *)
