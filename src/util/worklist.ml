(*
 * worklist.ml --- work lists
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

module Dq = Deque

type 'a wl = { add : 'a -> unit ;
               next : unit -> 'a ;
               get : unit -> 'a list ;
               clear : unit -> unit }

let create () =
  let store = ref (Dq.empty) in
  let add e = store := Dq.snoc (!store) e in
  let next () = match Dq.front (!store) with
    | Some (e, q) ->
        store := q ;
        e
    | None -> failwith "next" in
  let get () = Dq.to_list (!store) in
  let clear () = store := Dq.empty in
    { add = add ;
      next = next ;
      get = get ;
      clear = clear }

let with_wl f =
  let wl = create () in
    f wl ;
    wl.get ()
