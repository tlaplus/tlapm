type language_feature =
  | RecursiveOperator
  | Subexpression

exception Unsupported_language_feature of Loc.locus option * language_feature
val parse : string -> (Module.T.modctx * Module.T.mule, string option * string) result