(** Proof step, as it is displayed in the editor. The proof steps are obtained
    by parsing the TLAPS source file. Later the proof obligation info is added
    to the tree as they are obtained from the prover. *)

open Util

module El : sig
  type t =
    | Module of TL.Module.T.mule
    | Theorem of {
        mu : TL.Module.T.modunit;
        name : TL.Util.hint option;
        sq : TL.Expr.T.sequent;
        naxs : int;
        pf : TL.Proof.T.proof;
        orig_pf : TL.Proof.T.proof;
        summ : TL.Module.T.summary;
      }
    | Mutate of { mu : TL.Module.T.modunit; usable : TL.Proof.T.usable }
    | Step of TL.Proof.T.step
    | Qed of TL.Proof.T.qed_step
  [@@deriving show]
end

type t [@@deriving show]

val of_module : ?prev:t -> Tlapm_lib.Module.T.mule -> t option
val el : t -> El.t * TL.Expr.T.ctx
val goal : t -> TL.Proof.T.obligation option
val proof : t -> TL.Proof.T.proof option
val full_range : t -> Range.t
val head_range : t -> Range.t

val step_name : t -> TL.Proof.T.stepno option
(** Returns a level and a name of the proof step. [None] is returned if that's a
    module-level element. *)

val sub_step_label_seq : t -> int Seq.t
(** Returns a sequence of fresh step names to be used for sub-steps of the
    provided proof step. *)

val sub_step_name_seq : t -> TL.Proof.T.stepno Seq.t
(** Returns a sequence of fresh step names to be used as sub-steps. *)

val sub_step_unnamed : t -> TL.Proof.T.stepno
(** Produces a "unnamed" step number for a sub-step of a given step. *)

(** {1 Modifiers.} *)

val with_prover_terminated : t option -> int -> t option

val with_prover_result :
  t option -> int -> Prover.Toolbox.Obligation.t -> t option

val with_provers : t option -> int -> int -> string list -> t option

(** {1 Queries} *)

val locate_proof_path : t -> Range.t -> t list
(** Finds the first deepest proof step covered by the specified range. The
    result contains the deepest proof step, or an empty list, if no matching
    step was found at all. *)

val locate_proof_step : t option -> Range.Position.t -> t option
val locate_proof_range : t option -> Range.t -> Range.t
val is_obl_final : t option -> int -> int -> bool option
val flatten : t option -> t list
val fold : ('a -> t -> 'a) -> 'a -> t option -> 'a
val fold_obs : ('a -> Obl.t -> 'a) -> 'a -> t -> 'a

(** {1 Conversions} *)

val as_lsp_tlaps_proof_state_marker : t -> Structs.TlapsProofStepMarker.t

val as_lsp_tlaps_proof_step_details :
  LspT.DocumentUri.t -> t -> Structs.TlapsProofStepDetails.t
