(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)
open Property
open Expr.T


type omission =
  | Implicit
  | Explicit
  | Elsewhere of Loc.locus
type proof = proof_ wrapped
and proof_ =
  | Obvious
  | Omitted of omission
  | By      of usable * bool
  | Steps   of step list * qed_step
  | Error   of string
(** Non-terminal proof steps *)
and step = step_ wrapped
and step_ =
  | Hide     of usable
  | Define   of defn list
  | Assert   of sequent * proof
  | Suffices of sequent * proof
  | Pcase    of expr * proof
  | Pick     of bound list * expr * proof
  | Use      of usable * bool
  | Have     of expr
  | Take     of bound list
  | Witness  of expr list
  | Forget   of int
(** Terminal proof-step **)
and qed_step = qed_step_ wrapped
and qed_step_ =
  | Qed of proof
(** Usable elements *)
and usable = { facts : expr list
             ; defs  : use_def wrapped list }

and use_def =
  | Dvar of string
  | Dx   of int


(*
type isequent = private {
  isq : sequent;
  idx : unit;  (* FIXME add index *)
}
*)


(* There are three kinds of obligations:

   Main -> the main obligation of a BY or OBVIOUS
   Support -> the obligations for the elements of a BY or USE
   Error -> a special obligation that carries an error message to the user
*)
type obligation_kind =
  | Ob_main
  | Ob_support
  | Ob_error of string
type obligation = {
  id  : int option;
  obl : sequent wrapped;
  fingerprint : string option;
    kind: obligation_kind}


type stepno =
  | Named   of int * string * bool
  | Unnamed of int * int


module Props : sig
  val step : stepno pfuncs
  val goal : sequent pfuncs
  val supp : unit pfuncs
  val obs : obligation list pfuncs
  val meth : Method.t list pfuncs
  val orig_step : step pfuncs
  val orig_proof : proof pfuncs
  val use_location : Loc.locus pfuncs
end


val string_of_stepno:
    ?anonid:bool -> stepno -> string
(* `proof/p_subst.ml` *)
val get_qed_proof:
    qed_step_ Property.wrapped -> proof
(* `proof/p_simplify.ml` *)
val step_number: stepno -> int
