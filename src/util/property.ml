(*
 * property.ml --- properties
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Property lists implemented using unsafe ocaml features *)

Revision.f "$Rev$";;

open Ext

type uuid = Int64.t * Int64.t

let uuid_of_string s : uuid =
  assert (String.length s = 36) ;
  assert (s.[8] = '-' && s.[13] = '-' && s.[18] = '-' && s.[23] = '-') ;
  Scanf.sscanf s "%8Lx-%4Lx-%4Lx-%4Lx-%12Lx" begin
    fun a b c d e ->
      let a = Int64.shift_left a 32 in
      let b = Int64.shift_left b 16 in
      let l = Int64.logor (Int64.logor a b) c in
      let d = Int64.shift_left d 48 in
      let r = Int64.logor d e in
      (l, r)
  end

type pid =
  | Pid of int
  | Puuid of uuid

type prop = pid * Obj.t

type props = prop list

type 'a pfuncs = {
  get : prop -> 'a ;
  set : 'a -> prop ;
  pid : pid ;
  rep : string ;
}

let ids : int ref = ref 0

let fresh () = incr ids ; !ids

let pid (id, _) = id

let make ?uuid rep =
  let pid = match uuid with
    | Some uus -> Puuid (uuid_of_string uus)
    | None -> Pid (fresh ())
  in
  let set x = (pid, Obj.repr x) in
  let get (qid, ob) =
    if pid = qid then Obj.obj ob
    else invalid_arg "Property.get"
  in
    { get = get ; set = set
    ; pid = pid ; rep = rep }

type 'a wrapped = {
  core : 'a ;
  props : props ;
}

let has w pf =
  List.exists (fun p -> pf.pid = fst p) w.props

let get w pf =
  pf.get (List.find (fun p -> pf.pid = fst p) w.props)

let query w pf =
  try Some (pf.get (List.find (fun p -> pf.pid = fst p) w.props)) with
    | Not_found -> None

let assign w pf v =
  { w with props = pf.set v :: List.filter (fun p -> pf.pid <> fst p) w.props }

let remove w pf =
  { w with props = List.filter (fun p -> pf.pid <> fst p) w.props }

let noprops x = { core = x ; props = [] }

let nowhere : unit wrapped = noprops ()

(* adds (only) new properties from bw to aw *)
let ( $$ ) aw bw =
  let forall_fun i2 = function
    | (Pid i,_) -> i <> i2
    | _ -> true in
  let filter_fun = function
    | (Pid i,_) -> List.for_all (forall_fun i) aw.props
    | _ -> true in
  let pr = List.append aw.props (List.filter filter_fun bw.props) in
  {aw with props = pr}

let ( @@ ) a bw = { bw with core = a }

let ( %% ) a ps = { core = a ; props = ps }

(** {6 unsafe} *)

let unsafe_con e =
  let er = Obj.repr e.core in
    Obj.tag er

external props_of_value : 'a -> props = "%field0"

let props_of a =
  if Obj.is_int (Obj.repr a) then props_of_value a     (* FIXME BUG *)
  else invalid_arg "props_of"

let unsafe_has a pf =
  List.exists (fun p -> pf.pid = fst p) (props_of a)

let unsafe_get a pf = (* should this be really unsafe ? *)
  try pf.get (List.find (fun p -> pf.pid = fst p) (props_of a))
  with Not_found -> assert false

let unsafe_query a pf =
  try Some (pf.get (List.find (fun p -> pf.pid = fst p) (props_of a))) with
    | Not_found -> None

let unsafe_assign (a : 'a) pf v : 'a =
  let br = Obj.dup (Obj.repr a) in
    Obj.set_field br 0 begin
      Obj.repr (pf.set v :: List.filter (fun p -> pf.pid <> fst p) (props_of a))
    end ;
    Obj.obj br


let print_prop = function
  | (Pid i, _) -> print_int i
  | (Puuid (i1,i2), _) ->  print_string (Int64.to_string i1); print_string (Int64.to_string i2)

let print_all_props = function
  | {props = ls} -> List.iter print_prop ls

