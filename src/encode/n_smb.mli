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


(* {3 Symbols} *)

(** A symbol is essentially defined by a name and a type.  The implementation
    is made generic on the type 'a, which may be used to record any additional
    information that define a symbol.
*)
type 'a smb

val mk_smb : string -> ty2 -> 'a -> 'a smb

val get_name : 'a smb -> string
val get_ty2  : 'a smb -> ty2
val get_ty1  : 'a smb -> ty1  (** May raise {!Type.T.Invalid_type_downcast} *)
val get_ty0  : 'a smb -> ty0  (** May raise {!Type.T.Invalid_type_downcast} *)
val get_ord  : 'a smb -> int
val get_defn : 'a smb -> 'a


(* {3 Operations} *)

val fold : ('b -> 'a -> 'b) -> 'b -> 'a smb -> 'b
val map  : ('a -> 'b) -> 'a smb -> 'b smb
val iter : ('a -> unit) -> 'a smb -> unit


(* {3 Pretty-printing} *)

val pp_print_smb : ?pp_print_defn:(Format.formatter -> 'a -> unit) -> Format.formatter -> 'a smb -> unit

