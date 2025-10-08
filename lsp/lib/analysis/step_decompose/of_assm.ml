open Util

(** Propose proof decomposition CodeAction for an assumption in the form of
    disjunction.
    - The proof is split to multiple steps "by cases", in the same level as the
      QED step for which the action is proposed.
    - The decomposition is only proposed if the current context don't have one
      of the disjuncts among the assumptions. This way we don't repeat proposing
      the same. *)
(*  TODO
let cas_of_assm_disj (_uri : LspT.DocumentUri.t) (_ps : PS.t)
    (_ps_parent : PS.t) _cx _disjuncts =
  (* TODO *)
  [] *)

let code_actions (_uri : LspT.DocumentUri.t) (_ps : PS.t) (_ps_parent : PS.t)
    (_cx : TL.Expr.T.ctx) =
  []
