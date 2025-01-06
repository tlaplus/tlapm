(** Obligation reference consists of the proof session reference (p_ref) and the
    obligation id (obl_id) as assigned by the TLAPS. This reference is unique
    across proof attempts. *)
module OblRef = struct
  type t = { p_ref : int; obl_id : int }

  let make ~p_ref ~obl_id = { p_ref; obl_id }

  let compare a b =
    let p_ref_cmp = Stdlib.compare a.p_ref b.p_ref in
    if p_ref_cmp = 0 then Stdlib.compare a.obl_id b.obl_id else p_ref_cmp
end

module LspT = Lsp.Types
module DocMap = Map.Make (LspT.DocumentUri)
module OblMap = Map.Make (OblRef)
module StrMap = Map.Make (String)
module RangeMap = Map.Make (Range)

type parser_fun =
  content:string ->
  filename:string ->
  (Tlapm_lib.Module.T.mule, string option * string) result
