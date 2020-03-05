(*  Copyright 1997 INRIA  *)

open Expr;;

exception NoProof;;
exception LimitsExceeded;;

type branch_state =
  | Open
  | Closed of Mlproof.proof
  | Backtrack
;;

type rule;;
type params = {
  rules : rule list;
  fail : unit -> branch_state;
  progress : unit -> unit;
  end_progress : string -> unit;
};;

val prove : params -> definition list -> (expr * int) list -> Mlproof.proof;;
val default_params : params;;

val newnodes_absurd : rule;;
val newnodes_closure : rule;;
val newnodes_eq_str : rule;;
val newnodes_jtree : rule;;
val newnodes_alpha : rule;;
val newnodes_beta : rule;;
val newnodes_delta : rule;;
val newnodes_gamma : rule;;
val newnodes_unfold : rule;;
val newnodes_refl : rule;;
val newnodes_match_congruence : rule;;
val newnodes_match_trans : rule;;
val newnodes_match_sym : rule;;
val newnodes_match : rule;;
val newnodes_preunif : rule;;
val newnodes_useless : rule;;
val newnodes_extensions : rule;;
