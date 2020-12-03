(*
 * loc.ml --- source locations
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

type pt_ = { line : int ;
              bol : int ;
              col : int ;
            }

type pt = Actual of pt_ | Dummy

let dummy = Dummy

type locus = { start : pt ;
               stop  : pt ;
               file : string ;
             }

let left_of l = { l with stop = l.start }
let right_of l = { l with start = l.stop }

let unknown = {
  start = Dummy ;
  stop  = Dummy ;
  file  = "<unknown>" ;
}

let column = function
  | Actual l -> l.col
  | Dummy -> failwith "Loc.column"

let line = function
  | Actual l -> l.line
  | Dummy -> failwith "Loc.line"

let offset = function
  | Actual l -> l.bol + l.col
  | Dummy -> failwith "Loc.offset"

let locus_of_position lp =
  let pt = { line = lp.Lexing.pos_lnum ;
             bol = lp.Lexing.pos_bol ;
             col = lp.Lexing.pos_cnum - lp.Lexing.pos_bol + 1 ;
           }
  in { start = Actual pt ;
       stop  = Actual pt ;
       file  = lp.Lexing.pos_fname ;
     }

let merge r1 r2 =
  if r1.file <> r2.file then
    failwith ("Loc.merge: " ^ r1.file ^ " <> " ^ r2.file)
  else
    try {
      start = if offset r1.start <= offset r2.start then r1.start else r2.start ;
      stop  = if offset r1.stop  >= offset r2.stop  then r1.stop  else r2.stop  ;
      file = r1.file
    } with _ -> unknown

let string_of_locus ?(cap = true) r =
  let ftok = if cap then "File" else "file" in
    match r.start, r.stop with
      | Actual start, Actual stop ->
          if start.line = stop.line && start.col >= stop.col - 1 then
            Printf.sprintf "%s %S, line %d, character %d"
              ftok r.file start.line start.col
          else
            (* || start.line <> stop.line
             * || start.bol <> stop.bol
             *)
            if start.line = stop.line then
              Printf.sprintf "%s %S, line %d, characters %d-%d"
                ftok r.file start.line start.col (stop.col - 1)
            else
              (* start.line <> stop.line *)
              Printf.sprintf "%s %S, line %d, character %d to line %d, character %d"
                ftok r.file
                start.line start.col
                stop.line (stop.col - 1)
      | _ ->
          Printf.sprintf "%s %S" ftok r.file

let string_of_locus_nofile r =
  match r.start, r.stop with
    | Actual start, Actual stop ->
        if start.line = stop.line && start.col >= stop.col - 1 then
          Printf.sprintf "line %d, character %d"
            start.line start.col
        else
          (* || start.line <> stop.line
           * || start.bol <> stop.bol
           *)
          if start.line = stop.line then
            Printf.sprintf "line %d, characters %d-%d"
              start.line start.col (stop.col - 1)
          else
            (* start.line <> stop.line *)
            Printf.sprintf "line %d, character %d to line %d, character %d"
              start.line start.col
              stop.line (stop.col - 1)
    | _ -> "<unknown location>"

let string_of_pt ?(file="<nofile>") l =
  string_of_locus { start = l ; stop = l ; file = file }

let compare r s =
  match Pervasives.compare (line r.start) (line s.start) with
    | 0 ->
        Pervasives.compare (column r.start) (column s.start)
    | c -> c
