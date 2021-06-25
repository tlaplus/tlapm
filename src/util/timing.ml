(*
 * timing.ml --- time tracking
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(**********************************************)
(* Simple timers *)

type timer = float

let start_timer () = Unix.gettimeofday ()

let get_timer t = Unix.gettimeofday () -. t

(**********************************************)
(* Old clock stuff (remove?) *)

type clock = { desc : string ;
               mutable time : float ;
               mutable count : int }

let new_clock desc = { desc = desc ;
                       time = 0.0 ;
                       count = 0 }

let ambient = new_clock "other"

let beginning_of_the_world = Unix.gettimeofday ()

let last_start = ref (ambient, beginning_of_the_world)

let start cl =
  let now = Unix.gettimeofday () in
  cl.count <- cl.count + 1;
  let (ocl, before) = !last_start in
  ocl.time <- ocl.time +. now -. before;
  last_start := (cl, now)

let stop () = start ambient

let total desc = {
    desc = desc;
    time = Unix.gettimeofday () -. beginning_of_the_world;
    count = 0;
  }

let string_of_clock cl =
  if (fst !last_start).desc == cl.desc then start cl ;
  Printf.sprintf "%s | %-13.6f" cl.desc cl.time
