(* TLA+ proof syntax tree, and relevant functions.

Copyright (C) 2008-2010  INRIA and Microsoft Corporation
*)
open Property
open Expr.T


type stepno =
    | Named of int * string * bool
    | Unnamed of int * int
    [@@deriving show]


let step_number = function
    | Named (n, _, _)
    | Unnamed (n, _) -> n


let string_of_stepno ?(anonid=false) = function
    | Named (sn, sl, _) ->
        Printf.sprintf "<%d>%s" sn sl
    | Unnamed (sn, sid) ->
        if anonid then
            Printf.sprintf "<%d>(*%d*)" sn sid
        else
            Printf.sprintf "<%d>" sn


type omission =
    | Implicit
    | Explicit
    | Elsewhere of Loc.locus


(** Proofs *)
type proof = proof_ wrapped
and proof_ =
    | Obvious
    | Omitted of omission
    | By of usable * bool
    | Steps of step list * qed_step
    | Error of string
(** Non-terminal proof steps *)
and step = step_ wrapped
and step_ =
    | Hide of usable
    | Define of defn list
    | Assert of sequent * proof
    | Suffices of sequent * proof
    | Pcase of expr * proof
    | Pick of bound list * expr * proof
    | PickTuply of tuply_bounds * expr * proof
    | Use of usable * bool
    | Have of expr
    | Take of bound list
    | TakeTuply of tuply_bounds
    | Witness of expr list
    | Forget of int
(** Terminal proof-step **)
and qed_step = qed_step_ wrapped
and qed_step_ =
    | Qed of proof
(** Usable elements *)
and usable = {
    facts: expr list;
    defs: use_def wrapped list}
and use_def =
    | Dvar of string
    | Dx of int


let get_qed_proof q =
    match q.core with Qed p -> p


type obligation_kind =
    | Ob_main
    | Ob_support
    | Ob_error of string


type obligation = {
    id: int option;
    obl: sequent wrapped;
    fingerprint: string option;
    kind: obligation_kind}


module Props = struct
    let step: stepno Property.pfuncs =
        Property.make
            ~uuid:"bb05cbe0-93a0-4fb7-aef8-55bee144b1e3"
            "Proof.Props.step"
    let goal: sequent pfuncs =
        Property.make
            ~uuid:"94caf0e0-64b6-4e79-b479-f958d089f46f"
            "Proof.Props.goal"
    let supp: unit pfuncs =
        Property.make
            ~uuid:"b6af5d62-bf07-4b79-b489-fbaf3e9cc3ba"
            "Proof.Props.supp"
    let obs: obligation list pfuncs =
        Property.make
            ~uuid:"6b493e40-a604-4cfa-9a13-a20a6808aea8"
            "Proof.Props.obs"
    let meth: Method.t list pfuncs =
        Property.make
            ~uuid:"c213e558-b21d-4356-97db-bd15f201510b"
            "Proof.Props.meth"
    let orig_step: step Property.pfuncs =
        Property.make
            ~uuid:"557d3bc3-8767-4b4f-96c1-ef90cce34a0c"
            "Proof.Props.orig_step"
    let orig_proof: proof Property.pfuncs =
        Property.make
            ~uuid:"15890d47-4fae-410a-a2fb-74a885d6f42f"
            "Proof.Props.orig_proof"
    let use_location: Loc.locus Property.pfuncs =
        Property.make
            "Proof.Props.use_location"
end
