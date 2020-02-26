(*
 * encode/table.ml --- table of symbols used to encode POs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Type.T
open Property

module B = Builtin

type family =
  | Sets | Booleans | Strings
  | Functions | Records | Tuples
  | Sequences | Arithmetic

type more_builtin =
  | Choose
  | SetSt
  | SetOf
  | SetEnum of int
  | Product of int
  | Tuple of int
  | Fcn
  | FcnApp
  | Arrow
  | Rect
  | Record
  | Except
  | Dot

type special =
  | Any of ty_atom
  | Cast of ty_atom * ty_atom

type smb =
  | Builtin of Builtin.builtin
  | MoreBuiltin of more_builtin
  | Special of special

type op =
  { idt : string
  ; fam : family
  ; ins : ty_kind list
  ; out : ty
  ; def : smb
  }

let ops = [
  Sets,
  List.map (fun (nm, ins, out, b) ->
    (nm, List.map mk_atom_ty ins |> List.map mk_cstk_ty, mk_atom_ty out, Builtin b))
  [ "mem",      [ TU ; TU ],  TBool,  B.Mem
  ; "subseteq", [ TU ; TU ],  TBool,  B.Subseteq
  (* TODO *)
  ]
]

let table =
  let module H = Hashtbl in
  let tab = H.create 150 in
  List.iter begin fun (fam, ops) ->
    List.iter begin fun (nm, ins, out, smb) ->
      let op =
        { idt = nm
        ; fam = fam
        ; ins = ins
        ; out = out
        ; def = smb
        }
      in
      H.add tab smb op
    end ops
  end ops;
  tab

let make_op smb =
  match smb with
  | MoreBuiltin (SetEnum n) ->
      { idt = "setenum_" ^ string_of_int n
      ; fam = Sets
      ; ins = List.init n (fun _ -> mk_atom_ty TU |> mk_cstk_ty)
      ; out = mk_atom_ty TU
      ; def = smb
      }
  | _ -> Errors.bug "Encode.Table.make_op: unrecognized symbol"

let lookup_op smb =
  if Hashtbl.mem table smb then
    Hashtbl.find table smb
  else
    let op = make_op smb in
    Hashtbl.add table smb op;
    op

let special_prop = make "Encoding.Table.special_prop"

let to_hint op =
  let h = op.idt %% [] in
  let h = assign h special_prop op.def in
  let k = mk_kind_ty op.ins op.out in
  let h = annot_kind h k in
  h
