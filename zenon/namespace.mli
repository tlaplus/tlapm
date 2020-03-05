(*  Copyright 2006 INRIA  *)

val prefix : string;;         (* prefix of all the following *)

val anon_prefix : string;;    (* anonymous hypotheses *)
val builtin_prefix : string;; (* built-in symbols *)
val dummy_prefix : string;;   (* dummy local idents *)
val hyp_prefix : string;;     (* local hypotheses *)
val lemma_prefix : string;;   (* lemmas *)
val tau_prefix : string;;     (* skolem constants *)
val var_prefix : string;;     (* gensym variables *)
val meta_prefix : string;;    (* meta variables *)

val goal_name : string;;      (* the goal *)
val any_name : string;;       (* an element of the universe *)
val univ_name : string;;      (* the 1st-order universe *)

val thm_default_name : string;; (* default name of the theorem *)

val tuple_name : string;;     (* built-in constructor for tuples *)
