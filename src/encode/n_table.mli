(*
 * encode/table.mli --- table of symbols used to encode POs
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Type.T

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

val table : (smb, op) Hashtbl.t

val lookup_op : smb -> op

val special_prop : smb Property.pfuncs
val to_hint : op -> Util.hint
