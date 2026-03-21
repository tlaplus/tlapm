type language_feature =
  | RecursiveOperator
  | InstanceProofStep
  | Subexpression

exception Unsupported_language_feature of Loc.locus option * language_feature

type conversion_failure_kind =
  | NotYetImplemented
  | InvalidBoundsOrOperands

exception Conversion_failure of conversion_failure_kind * string option * string

val parse : string -> (Module.T.modctx * Module.T.mule, string option * string) result

open Sexplib;;
val module_to_sexp : Module.T.mule -> Sexp.t
