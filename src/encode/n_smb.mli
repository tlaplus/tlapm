(*
 * encode/smb.mli --- symbols for expressions in standard form
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Symbols offer a common representation for TLA+ operators, builtins, and
    primitive constructs.  Using symbols, every TLA+ expression can be put in
    a standard form.  An expression in standard form does not contain
    primitives that fall outside of first-order logic with second-order
    application.  (Temporal logic is ignored).

    The principle of this representation is to encode primitive constructs
    using symbols.  For instance: [a \cup b] is represented by [cup(a, b)],
    where [cup] is a symbol.  With second-order application, every expression
    can be represented as an application: [{ x \in a : P }] may also be written
    [setst(a, LAMBDA x : P)] where [setst] is a symbol.
*)

open Type.T
open Property

open N_table


(* {3 Symbols} *)

type smb_kind = Untyped | Typed | Special

type smb

val smb_prop : smb pfuncs

module SmbSet : Set.S with type elt = smb

val mk_smb : ?tver:tla_smb -> tla_smb -> smb

(** Use this function rather than (=) *)
val equal_smb : smb -> smb -> bool

val get_name : smb -> string
val get_ty2  : smb -> ty2
val get_ty1  : smb -> ty1  (** May raise {!Type.T.Invalid_type_downcast} *)
val get_ty0  : smb -> ty0  (** May raise {!Type.T.Invalid_type_downcast} *)
val get_ord  : smb -> int

val get_defn  : smb -> tla_smb
val get_kind  : smb -> smb_kind
val get_tdefn : smb -> tla_smb  (** Raise {!Invalid_argument} is {!get_kind} does not return [Untyped] *)


(* {3 Pretty-printing} *)

val pp_print_smb : Format.formatter -> smb -> unit

