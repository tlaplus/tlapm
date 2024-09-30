(*
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *
 * WARNING: While this library is exposed for other projects, its interface
 * is considered experimentai and not stable. It can change in uncompatible
 * ways in the future.
 *)

module Module = Module
module Property = Property
module Proof = Proof
module Expr = Expr
module Util = Util
module Deque = Deque
module Loc = Loc
module Ctx = Ctx
module Backend = Backend
module Builtin = Builtin

val main : string list -> unit
val init : unit -> unit

val modctx_of_string :
  content:string ->
  filename:string ->
  loader_paths:string list ->
  prefer_stdlib:bool ->
  (Module.T.modctx * Module.T.mule, string option * string) result
(** Parse and elaborate the specified module and its context
    from a specified string, assume it is located in the
    specified path. *)

val module_of_string : string -> Module.T.mule option
(** Parse the specified string as a module. No dependencies
    are considered, nor proof obligations are elaborated. *)

val stdlib_search_paths : string list
(** A list of paths to look for stdlib modules. *)
