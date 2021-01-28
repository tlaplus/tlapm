(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(* pars/error.ml *)
val toolbox : bool ref;;

(* expr/fmt.ml *)
val debugging : string -> bool;;
val notl : bool ref;;

(* proof/gen.ml *)
val verbose : bool ref;;

(* backend/isabelle.ml *)
val check : bool ref;;
type exec;;
val output_dir : string ref;;
val wait : int ref;;

(* backend/prep.ml *)
val zenon_version : (string * int * int) option ref;;
val solve_cmd : exec -> string -> string;;
val zenon : exec;;
val isabelle_success_string : string;;
val isabelle : exec;;
val set_fast_isabelle : unit -> unit;;
val smt : exec;;
val cvc4 : exec;;
val yices : exec;;
val z3 : exec;;
val verit : exec;;
val zipper : exec;;
val spass_dfg : exec;;
val spass_tptp : exec;;
val eprover : exec;;
val ls4 : exec;;
val no_fp : bool ref;;
val nofp_sl : int ref;;
val nofp_el : int ref;;
val default_method : Method.t list ref;;
val printallobs : bool ref;;
val pr_normal : bool ref;;
val ob_flatten : bool ref;;
val noproving : bool ref;;

(* backend/server.ml *)
val max_threads : int ref;;
val path_prefix : string;;

(* backend/fingerprints.ml *)
val rawversion : unit -> string;;
val get_zenon_verfp : unit -> string;;
val get_isabelle_version : unit -> string;;
val fp_hist_dir : string ref;;
val fp_original_number : int ref;;
val safefp : bool ref;;

(* backend/toolbox.ml *)
val fp_deb : bool ref;;

(* util/util.ml *)
val configuration : bool -> bool -> string list;;

(* module/save.ml *)
val rev_search_path : string list ref;;
val self_sum : Digest.t;;
val use_xtla : bool ref;;
val xtla : bool ref;;

(* tlapm_args.ml *)
val rm_debug_flag : string -> unit;;
val add_debug_flag : string -> unit;;
val tb_sl : int ref;;
val tb_el : int ref;;
val input_files : string list ref;;
val set_default_method : string -> unit;;
val library_path : string;;
val cleanfp : bool ref;;
val fpf_in : string option ref;;
val summary : bool ref;;
val stats : bool ref;;
val add_search_dir : string -> unit;;
val keep_going : bool ref;;   (* FIXME check still used ? *)
val suppress_all : bool ref;;
val set_smt_solver : string -> unit;;
val printconfig : bool -> string;;
val print_config_toolbox : bool -> string;;
val check_zenon_ver : unit -> unit;;
val fpf_out : string option ref;;
val fp_loaded : bool ref;;
val timeout_stretch : float ref;;

(* encode/ *)
val enc_verbose : bool ref;;



val backend_timeout : float ref;;
