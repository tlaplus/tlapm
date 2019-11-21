(*
 * worklist.mli --- work lists
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

type 'a wl = { add : 'a -> unit ;
               next : unit -> 'a ;
               get : unit -> 'a list ;
               clear : unit -> unit }

val create : unit -> 'a wl

val with_wl : ('a wl -> unit) -> 'a list
