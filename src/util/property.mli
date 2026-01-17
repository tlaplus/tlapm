(*
 * property.mli --- properties
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Heterogeneous properties.

    Heavily influenced by a similar design in the MLton compiler. The
    idea is apparently folklore, though at least Stephen Weeks,
    Benjamin Pierce and Davide Sangiorgi have claimed to have
    (re-)invented it.

    By default this module uses type-unsafe features of the ocaml
    implementation. However, the ocaml type system is powerful enough
    to implement this module; an example using references can be seen
    in the [property_safe.ml] file.
*)

(** Property identifiers. They may be safely compared using
    [Stdlib.compare]. *)
type pid

(** The abstract type of "properties". All types can be injected and
    projected from this type safely. *)
type prop

type props = prop list

val pp_prop_name : Format.formatter -> prop -> unit
val pp_prop_names : Format.formatter -> props -> unit


(** [pid p] returns the pid of property [p]. All properties of the
    same pid store values of the same type (and this is statically
    enforced by the compiler). *)
val pid : prop -> pid

(** A type to represent the operations on properties of a given
    pid. The [get] function will throw an [Invalid_argument] exception
    if it is called on a property not created with its matching
    [set]. *)
type 'a pfuncs = {
  get : prop -> 'a ;
  set : 'a -> prop ;
  pid : pid ;
  rep : string ;
}

(** [make ()] creates a new property and returns its getters, setters
    and pid in as a [pfuncs]. In most cases, this function can only be
    used monomorphically. If the optional argument [uuid] is provided,
    the returned property will have that pid. This is provided in
    order for (de)serialization of the PM's data structures. IT IS
    ABSOLUTELY UNSAFE TO REUSE UUIDS. *)
val make : ?uuid:string -> string -> 'a pfuncs

(** An object wrapped with a property map. By the nature of [PMap.t],
    there can be at-most one instance of every pid among the
    [props]. In order to weaken this restriction, a different map type
    (and corresponding wrapper functions) must be defined by the
    user. *)
type 'a wrapped = {
  core  : 'a ;
  props : props ;
}

(** [has w pf] checks if the properties of [w] include any with pid
    [pf.pid]. *)
val has    : 'a wrapped -> 'b pfuncs -> bool

(** [get w pf] looks up the value of any property with pid [pf.pid] in
    the properties of [w]. Raises [Not_found] if not [has w pf]. *)
val get    : 'a wrapped -> 'b pfuncs -> 'b

(** [query w pf] looks up the value of any property with pid [pf.pid]
    in the properties of [w]. *)
val query  : 'a wrapped -> 'b pfuncs -> 'b option

(** [assign w pf v] assigns the property witih pid [pf.pid] the value
    [v] in the properties of [w]. Adds this property to [w] if it
    doesn't already exist. *)
val assign : 'a wrapped -> 'b pfuncs -> 'b -> 'a wrapped

(** An [|>] friendly variant of [assign]. *)
val with_prop : 'b pfuncs -> 'b -> 'a wrapped -> 'a wrapped

(** [remove w pf] removes the property with pid [wf.pid] (if any) from
    [w]. *)
val remove : 'a wrapped -> 'b pfuncs -> 'a wrapped

(* `unwrap x` returns `x.core`.
Useful for use with `List.map`.
*)
val unwrap: 'a wrapped -> 'a

(** [noprops x] wraps [x] with no properties. *)
val noprops : 'a -> 'a wrapped

(** [nowhere] is a wrapped value with no properties. *)
val nowhere : unit wrapped

(** [aw $$ bw] returns aw with all new properties in bw *)
val ( $$ ) : 'a wrapped -> 'b wrapped -> 'a wrapped

(** [x @@ w] wraps [x] with the properties of [w] *)
val ( @@ ) : 'a -> 'b wrapped -> 'a wrapped

val ( %% ) : 'a -> props -> 'a wrapped

(** {6 Unsafe stuff} *)

val unsafe_con : 'a wrapped -> int

(** in all of the following functions, the first argument is assumed
    to be non-empty tuple, array or record whose first field is a prop
    list, or a case of a datatype with a non-empty constructor whose
    first field is a prop list. THIS IS NOT CHECKED. Calling them on
    any other kind of object will probably cause a segmentation
    fault. *)

val props_of : 'a -> props
val unsafe_has     : 'a -> 'b pfuncs -> bool
val unsafe_get     : 'a -> 'b pfuncs -> 'b
val unsafe_query   : 'a -> 'b pfuncs -> 'b option
val unsafe_assign  : 'a -> 'b pfuncs -> 'b -> 'a

(** printer for properties *)
val print_all_props : 'a wrapped -> unit
