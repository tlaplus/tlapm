(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

open Property
open Util

open Expr.T
open Proof.T


(* module/m_fmt.ml *)
type mule = mule_ wrapped
and mule_ = {
    name: hint;
    extendees: hint list;  (* module names
        from `EXTENDS` statements *)
    instancees: hint list;  (* module names
        from `INSTANCE` statements,
        only external instancees *)
    body: modunit list;
    defdepth: int;  (* context depth:
        number of declarations and
        definitions (TODO: confirm) *)
    mutable stage: stage;
    mutable important: bool}
(** module unit *)
and modunit = modunit_ wrapped
and modunit_ =
    | Constants of (hint * shape) list
    | Recursives of (hint * shape) list
    | Variables of hint list
    | Definition of
        defn * wheredef * visibility * export
    | Axiom of hint option * expr
    | Theorem of
        hint option * sequent * int *
        proof * proof * summary
    | Submod of mule
    | Mutate of
        [`Use of bool | `Hide] * usable
    | Anoninst of instance * export
and named = Named | Anonymous
and summary = {
    sum_total: int;
    sum_absent: int * Loc.locus list;
    sum_omitted: int * Loc.locus list;
    sum_suppressed: int * Loc.locus list}
and stage =
    | Special
    | Parsed | Flat
    | Final of final
and final = {
    final_named: modunit list;
    final_obs: obligation array;
    final_status: status * summary}
and status =
    | Unchecked | Proved
    | Certified | Incomplete
type modctx = mule Coll.Sm.t


(* module/m_gen.ml *)
val empty_summary: summary
val cat_summary:
    summary -> summary -> summary
val hyps_of_modunit:
    modunit ->
        Expr.T.hyp_ Property.wrapped list
(* module/m_elab.ml *)
val hyp_size: modunit -> int
val salt_prop: unit Property.pfuncs
