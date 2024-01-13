(** OblInfo collects related tlapm_obligation events into a single place.
    It maintains the general obligation info (initial) and the latest
    state for each of the provers.
    *)

type t = {
  initial : Tlapm_lsp_prover.ToolboxProtocol.tlapm_obligation;
  by_prover : Tlapm_lsp_prover.ToolboxProtocol.tlapm_obligation Util.StrMap.t;
  latest_prover : string option;
}

val make : Tlapm_lsp_prover.ToolboxProtocol.tlapm_obligation -> t
val add_obl : Tlapm_lsp_prover.ToolboxProtocol.tlapm_obligation -> t -> t
val latest : t -> Tlapm_lsp_prover.ToolboxProtocol.tlapm_obligation
val loc : t -> Tlapm_lsp_prover.TlapmRange.t
