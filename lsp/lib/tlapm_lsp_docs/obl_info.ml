open Util
open Tlapm_lsp_prover.ToolboxProtocol

type t = {
  initial : tlapm_obligation;
  by_prover : tlapm_obligation StrMap.t;
  latest_prover : string option;
}

let make obl = { initial = obl; by_prover = StrMap.empty; latest_prover = None }

let add_obl obl (oi : t) =
  match obl.prover with
  | None -> oi
  | Some prover ->
      let by_prover = StrMap.add prover obl oi.by_prover in
      { oi with by_prover; latest_prover = Some prover }

let latest (oi : t) =
  match oi.latest_prover with
  | None -> oi.initial
  | Some prover -> StrMap.find prover oi.by_prover

let loc (oi : t) = oi.initial.loc
