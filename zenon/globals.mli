(*  Copyright 1997 INRIA  *)

val debug_flag : bool ref;;

val stats_flag : bool ref;;
val quiet_flag : bool ref;;
val size_limit : float ref;;
val step_limit : float ref;;
val time_limit : float ref;;
val short_flag : bool ref;;
val ctx_flag : bool ref;;
val random_flag : bool ref;;
val random_seed : int ref;;
val load_path : string ref;;
val namespace_flag : bool ref;;
val use_all_flag : bool ref;;

val inferences : int ref;;
val proof_nodes : int ref;;
val top_num_forms : int ref;;
val stored_lemmas : int ref;;
val num_expr : int ref;;
