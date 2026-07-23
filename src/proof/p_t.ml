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

let sub_step_number (sn : stepno option) : int =
    match sn with
    | None -> 1
    | Some step -> (step_number step) + 1

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
    | Ob_omitted of omission


type obligation = {
    id: int option;
    obl: sequent wrapped;
    fingerprint: string option;
    kind: obligation_kind}


let pp_use_def fmt (ud : use_def) =
  match ud with
  | Dvar s -> Format.fprintf fmt "DVar[%s]" s
  | Dx i -> Format.fprintf fmt "Dx[%i]" i

let pp_usable ~pp_props (fmt : Format.formatter) (u : usable) =
  Format.(
    fprintf fmt "(@[Usable,@ facts=%a,@ defs=%a@])"
      (pp_print_list ~pp_sep:pp_print_cut (Expr.T.pp_expr ~pp_props))
      u.facts
      (pp_print_list ~pp_sep:pp_print_cut
         (pp_wrapped ~pp_props ~pp_core:pp_use_def))
      u.defs)

let pp_usable_wrapped ~pp_props (fmt : Format.formatter) (u : usable wrapped) =
  Format.fprintf fmt "%a"
    (pp_wrapped ~pp_props ~pp_core:(pp_usable ~pp_props))
    u

let rec pp_proof ~pp_props (fmt : Format.formatter) (pf : proof) =
  Format.fprintf fmt "%a"
    (pp_wrapped ~pp_props ~pp_core:(pp_proof_ ~pp_props))
    pf

and pp_proof_ ~pp_props (fmt : Format.formatter) (pf : proof_) =
  match pf with
  | Obvious -> Format.fprintf fmt "Obvious"
  | Omitted Implicit -> Format.fprintf fmt "Omitted/Implicit"
  | Omitted Explicit -> Format.fprintf fmt "Omitted/Explicit"
  | Omitted (Elsewhere _) -> Format.fprintf fmt "Omitted/Elsewhere"
  | By (usable, only) ->
      Format.fprintf fmt "(@[By[only=%b],@ %a@])" only (pp_usable ~pp_props)
        usable
  | Steps (inits, qed) ->
      Format.(
        fprintf fmt "(@[Steps,@ inits=%a,@ qed=%a@])"
          (pp_print_list ~pp_sep:pp_print_cut (pp_step ~pp_props))
          inits (pp_qed_step ~pp_props) qed)
  | Error s -> Format.fprintf fmt "Error[%s]" s

and pp_step ~pp_props (fmt : Format.formatter) (st : step) =
  Format.fprintf fmt "@[%a@]"
    (pp_wrapped ~pp_props ~pp_core:(pp_step_ ~pp_props))
    st

and pp_step_ ~pp_props (fmt : Format.formatter) (st : step_) =
  match st with
  | Hide usables ->
      Format.fprintf fmt "(@[Hide,@ %a@])" (pp_usable ~pp_props) usables
  | Define defns ->
      Format.(
        fprintf fmt "(@[Define,@ %a@])"
          (pp_print_list ~pp_sep:pp_print_cut (Expr.T.pp_defn ~pp_props))
          defns)
  | Assert (sq, pf) ->
      Format.fprintf fmt "(@[Assert,@ %a,@ %a@])"
        (Expr.T.pp_sequent ~pp_props)
        sq (pp_proof ~pp_props) pf
  | Suffices (sq, pf) ->
      Format.fprintf fmt "(@[Suffices,@ %a,@ %a@])"
        (Expr.T.pp_sequent ~pp_props)
        sq (pp_proof ~pp_props) pf
  | Pcase (ex, pf) ->
      Format.fprintf fmt "(@[Pcase,@ %a,@ %a@])" (Expr.T.pp_expr ~pp_props) ex
        (pp_proof ~pp_props) pf
  | Pick (bs, ex, pf) ->
      Format.fprintf fmt "(@[Pick,@ bounds=%a,@ ex=%a,@ pf=%a@])"
        (Expr.T.pp_bounds ~pp_props)
        bs (pp_expr ~pp_props) ex (pp_proof ~pp_props) pf
  | PickTuply (bs, ex, pf) ->
      Format.fprintf fmt "(@[PickTuply,@ bounds=%a,@ ex=%a,@ pf=%a@])"
        (Expr.T.pp_tuply_bounds ~pp_props)
        bs (pp_expr ~pp_props) ex (pp_proof ~pp_props) pf
  | Use (usable, only) ->
      Format.fprintf fmt "(@[Use[only=%b],@ %a@])" only (pp_usable ~pp_props) usable
  | Have ex -> Format.fprintf fmt "(@[Have,@ %a@])" (pp_expr ~pp_props) ex
  | Take bs -> Format.fprintf fmt "(@[Take,@ %a@])" (Expr.T.pp_bounds ~pp_props) bs
  | TakeTuply bs ->
      Format.fprintf fmt "(@[TakeTuply,@ %a@])" (Expr.T.pp_tuply_bounds ~pp_props) bs
  | Witness exs ->
      Format.(
        fprintf fmt "(@[Witness,@ %a@])"
          (pp_print_list ~pp_sep:pp_print_cut (pp_expr ~pp_props))
          exs)
  | Forget num -> Format.fprintf fmt "(@[Forget,@ %d@])" num

and pp_qed_step ~pp_props (fmt : Format.formatter) (qed : qed_step) =
  Format.fprintf fmt "%a"
    (pp_wrapped ~pp_props ~pp_core:(pp_qed_step_ ~pp_props))
    qed

and pp_qed_step_ ~pp_props (fmt : Format.formatter) (qed : qed_step_) =
  match qed with
  | Qed pf -> Format.fprintf fmt "(@[Qed,@ %a@])" (pp_proof ~pp_props) pf

let pp_omission (fmt : Format.formatter) (o : omission) =
  match o with
  | Implicit -> Format.fprintf fmt "Implicit"
  | Explicit -> Format.fprintf fmt "Explicit"
  | Elsewhere loc ->
      Format.fprintf fmt "(@[Elsewhere@ %a@])" Loc.pp_locus_compact loc

let pp_obligation_kind (fmt : Format.formatter) (ok : obligation_kind) =
  match ok with
  | Ob_main -> Format.fprintf fmt "Ob_main"
  | Ob_support -> Format.fprintf fmt "Ob_support"
  | Ob_error str -> Format.fprintf fmt "(@[Ob_error,@ %s@])" str
  | Ob_omitted om -> Format.fprintf fmt "(@[Ob_omitted %a@])" pp_omission om

let pp_obligation ~pp_props (fmt : Format.formatter) (o : obligation) =
  Format.fprintf fmt
    "(@[Obligation,@ id=%a, obl=%a@, fingerprint=%a@, kind=%a@])"
    (Format.pp_print_option Format.pp_print_int)
    o.id
    (Expr.T.pp_sequent_wrapped ~pp_props)
    o.obl
    (Format.pp_print_option Format.pp_print_string)
    o.fingerprint pp_obligation_kind o.kind

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
