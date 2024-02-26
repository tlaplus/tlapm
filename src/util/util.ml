(*
 * util.ml --- format utilities
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open Loc

module Deque = Deque

type hint = string wrapped
type hints = hint list

let pp_print_hint ff h = Format.pp_print_string ff h.core

module HC = struct
  type t = hint
  let compare x y = Stdlib.compare x.core y.core
end

module IC = struct
  type t = int
  let compare x y = Stdlib.compare x y
end

module Coll = struct
  module Im = Map.Make (IC)
  module Is = Set.Make (IC)
  module Sm = Map.Make (String)
  module Ss = Set.Make (String)
  module Sh = Weak.Make (struct
                           type t = string
                           let hash = Hashtbl.hash
                           let equal = (=)
                         end)
  module Hm = Map.Make (HC)
  module Hs = Set.Make (HC)
end

let prop : locus pfuncs = make ~uuid:"efa05a42-e82d-40a2-b130-9cfdb089a0d5" "Util.prop"

let get_locus lw = get lw prop
let set_locus lw l = assign lw prop l
let query_locus lw = query lw prop
let locate x l = set_locus (noprops x) l
let location ?(cap=true) lw = match query_locus lw with
  | None -> "<unknown location>"
  | Some loc -> string_of_locus ~cap:cap loc

(* FIXME get rid of nonl *)
let kfprintf ?debug ?at ?prefix ?nonl cont ff fmt =
  (* Print `prefix` only if `at` is not `None`. *)
  match debug with
  | Some dbg when not (Params.debugging dbg) ->
      Format.ikfprintf cont ff fmt
  | _ ->
     begin match at with
     | None -> ()
     | Some thing ->
        match query_locus thing with
        | None -> Format.fprintf ff "<unknown location>:@\n";
        | Some loc ->
           let str = string_of_locus ~cap:true loc in
           Format.fprintf ff "%s:@\n" str;
     end;
     let prefix = match debug with
       | None -> Option.default "Error: " prefix
       | Some dbg -> "Debug [" ^ dbg ^ "]: "
     in
     if at <> None then Format.fprintf ff "%s" prefix;
     let has_nl =
       let fmts = string_of_format fmt in
       String.length fmts >= 2
       && fmts.[String.length fmts - 1] = '.'
       && fmts.[String.length fmts - 2] = '@'
     in
     let fmt = match nonl with
       | None when not has_nl -> fmt ^^ format_of_string "@."
       | _ -> fmt
     in
     Format.kfprintf cont ff fmt


let sprintf ?debug ?at ?prefix ?nonl fmt =
  ignore (Format.flush_str_formatter ());
  kfprintf ?debug ?at ?prefix ?nonl
    (fun _ -> Format.flush_str_formatter ()) Format.str_formatter fmt


let fprintf ?debug ?at ?prefix ?nonl ff fmt =
  kfprintf ?debug ?at ?prefix ?nonl (fun _ -> ()) ff fmt


let eprintf ?debug ?at ?prefix ?nonl fmt =
  fprintf ?debug ?at ?prefix ?nonl Format.err_formatter fmt

let printf ?debug ?at ?prefix ?nonl fmt =
  fprintf ?debug ?at ?prefix ?nonl Format.std_formatter fmt


(* FIXME remove, replace with assert false *)
exception Bug

(* FIXME remove, replace with assert false *)
let bug ?at msg =
  let bugmsg =
    let lines = [
      "Oops! This appears to be a bug in the TLA+ Proof Manager." ;
      "" ;
      "Please file a bug report, including as much information" ;
      "as you can. Mention the following in your report: " ;
      "" ]
      @ Params.configuration false false
    in
    String.concat "\n" lines ^ "\n"
  in
  (*Backend.Toolbox.print_message "error" msg ^"\n"^bugmsg;*)
  eprintf ?at ~prefix:"BUG: " "%s\n%s%!" msg bugmsg ;
  raise Bug

exception Not_implemented

let not_implemented ?at msg =
  eprintf ?at ~prefix:"NOT IMPLEMENTED: " "%s" msg ;
  raise Not_implemented

type csum = int * int

let checksum f =
  let scmd = Printf.sprintf "sum %s" f in
  let sin = Unix.open_process_in scmd in
  let hash = Std.input_all sin in
  ignore (Unix.close_process_in sin) ;
  Scanf.sscanf hash "%d %d" (fun j k -> (j, k))

let pp_print_csum ff (j, k) =
  Format.fprintf ff "<%d-%d>" j k

let plural ?(ending="s") count s =
  if count <> 1 then s ^ ending else s

let line_wrap ?(cols=70) s =
  let slen = String.length s in
  let buf = Buffer.create slen in
  let rec next_space x =
    if x >= slen then slen
    else if s.[x] = ' ' then x
    else next_space (x + 1)
  in
  let rec drop_spaces x =
    if x >= slen then invalid_arg "drop_spaces"
    else if s.[x] = ' ' then drop_spaces (x + 1)
    else x
  in
  let rec spin x ccol =
    if x >= slen then () else
      let nx = next_space (x + 1) in
      if nx - x + ccol >= cols then begin
        Buffer.add_string buf "\n" ;
        spin (drop_spaces x) 0
      end else begin
        Buffer.add_substring buf s x (nx - x) ;
        spin nx (ccol + nx - x)
      end
  in
  spin 0 0 ;
  Buffer.contents buf

let heap_stats () =
  Gc.full_major () ;
  let st = Gc.stat () in
  eprintf "@.@.>>>>> HEAP STATS: live_words = %d <<<<<<@.@." st.Gc.live_words

let add_hook h f x =
  let old = !h in
  h := (fun () -> f x; old ())


let rm_temp_file fname =
  if not (Params.debugging "tempfiles") then begin
    try Sys.remove fname with _ -> ()
  end


let temp_file (clean_hook : (unit -> unit) ref) suffix =
  let (fname, chan) =
    Filename.open_temp_file ~temp_dir:!Params.output_dir ~mode:[Open_binary]
                            "tlapm_" suffix
  in
  let f () =
    close_out chan;
    rm_temp_file fname;
  in
  add_hook clean_hook f ();
  (fname, chan)


(*****************************************)

exception Internal_timeout

let handler _ = raise Internal_timeout

(* Note: we are using SIGALRM and the real-time alarm system because
   SIGVTALRM and the virtual-time alarm system are not available on Cygwin *)

let set_timer t =
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle handler);
  ignore (Unix.setitimer Unix.ITIMER_REAL
    {Unix.it_interval = 0.02; Unix.it_value = t})


let clear_timer () =
  Sys.set_signal Sys.sigalrm Sys.Signal_ignore;
  ignore (Unix.setitimer Unix.ITIMER_REAL
    {Unix.it_interval = 0.; Unix.it_value = 0.})


let run_with_timeout tmo f x =
  try
    set_timer tmo;
    let result = f x in
    clear_timer ();
    Some result
  with Internal_timeout -> clear_timer (); None
