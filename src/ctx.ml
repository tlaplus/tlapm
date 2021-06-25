(* Generic contexts.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open Ext


type ident = { rep : string ; salt : int }

let string_of_ident id = match id.salt with
  | 0 -> id.rep
  | _ -> id.rep ^ "_"^ string_of_int id.salt

module EMap (Ord : Map.OrderedType) = struct
  module Underlying = Map.Make (Ord)
  include Underlying
  let maybe_find x m =
    try Some (find x m) with _ -> None
end

module M = EMap (String)
module IM = EMap (struct
                    type t = ident
                    let compare = Stdlib.compare
                  end)

type 'a ctx = {
  linrep : (ident * 'a option) list ;
  idents : ident M.t ;
  defns  : ('a option * int) M.t ;
  length : int
}

let dot = { linrep = [] ;
            idents = M.empty ;
            defns  = M.empty ;
            length = 0 }

let length cx = cx.length

let alter cx n how =
  if n <= 0 || n > cx.length then invalid_arg "Ctx.alter" ;
  let (backs, fronts) = List.split_nth (n - 1) cx.linrep in
  match fronts with
    | (id, Some x) :: fronts ->
        let x = how id x in
        { cx with
            linrep = backs @ ((id, Some x) :: fronts) ;
            defns = M.add (string_of_ident id) (Some x, n) cx.defns }
    | _ -> failwith "Ctx.alter"

let map cx fn =
  let lr = List.mapi begin fun n -> function
    | (id, None) -> (id, None)
    | (id, Some x) -> (id, Some (fn (n + 1) x))
  end cx.linrep in
  let ds = M.map begin function
    | (None, n) -> (None, n)
    | (Some x, n) -> (Some (fn n x), n)
  end cx.defns in
  { cx with linrep = lr ; defns = ds }

let mem ident cx = M.mem ident cx.idents

let maybe_adj cx v a =
  let rec find_id cur =
    if M.mem (string_of_ident cur) cx.defns then
      find_id { cur with salt = cur.salt + 1 }
    else cur
  in
  let id = match M.maybe_find v cx.idents with
    | None ->
        { salt = 0 ; rep = v }
    | Some id ->
        { id with salt = id.salt + 1 }
  in
  let id = find_id id in
    { linrep = (id, a) :: cx.linrep ;
      idents = M.add v id cx.idents ;
      defns  = M.add (string_of_ident id) (a, cx.length) cx.defns ;
      length = cx.length + 1 }

let adj cx v a = maybe_adj cx v (Some a)

let bump cx = maybe_adj cx "" None

let find_dep cx v = match M.maybe_find v cx.idents with
  | None -> None
  | Some id ->
      let (a, dep) = M.find (string_of_ident id) cx.defns in
        Some (a, cx.length - dep)

let find cx v = match find_dep cx v with
  | Some (dat, _) -> dat
  | _ -> None

let depth cx v = Option.map snd (find_dep cx v)

let push cx v = adj cx v (length cx)

let to_list cx =
  let rec transfer l = function
    | [] -> l
    | (_, Some x) :: xs -> transfer (x :: l) xs
    | _ -> invalid_arg "to_list"
  in transfer [] cx.linrep

open Format

let index cx n = List.nth cx.linrep (n - 1)

let top cx = match cx.linrep with
  | [] -> failwith "Ctx.top"
  | (id, dat) :: _ -> (id, dat)

let front cx = fst (top cx)

let using cx v a fn =
  let cx = adj cx v a in
  let v = fst (top cx) in
    fn cx v

let pp_print_ident ff id =
  Format.fprintf ff "%s.%d" id.rep id.salt
  (* pp_print_string ff (string_of_ident id) *)

let pp_print_ctx fmt ff cx =
  let rec pp ff = function
    | [] -> ()
    | [u, None] ->
        fprintf ff "%a"
          pp_print_ident u
    | [u, Some a] ->
        fprintf ff "%a::%a"
          pp_print_ident u fmt a
    | (u, None) :: cx ->
        fprintf ff "%a,@ %a"
          pp cx pp_print_ident u
    | (u, Some a) :: cx ->
        fprintf ff "%a,@ %a::%a"
          pp cx pp_print_ident u fmt a
  in fprintf ff "@[<b0>%a@]" pp cx.linrep

type 'a t = 'a ctx
