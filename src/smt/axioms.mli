(************************************************************************
*  smt3.mli
*
*
************************************************************************)

val m_tla : Builtin.builtin -> string

type smtsort = U | SBool | SInt | SStr | SField | SOp

type t_map = {
    op : Builtin.builtin -> string ;
    print_sort : smtsort -> string ;
    apply : 'a. ?isinfix:bool -> Format.formatter -> string -> (Format.formatter -> 'a -> unit) -> 'a list -> unit ;
    quant : 'a. Format.formatter -> Expr.T.quantifier -> 'a option -> (string * smtsort) list -> (Format.formatter -> 'a -> unit) -> 'a -> unit ;
    ite : string option ;
    uminus : 'a. Format.formatter -> (Format.formatter -> 'a -> unit) -> 'a -> unit ;
}

val smtlib_map : t_map
val yices_map : t_map
val dfg_map : t_map
val fof_map : t_map

(* val m_uminus : t_map -> string -> string *)

val build_tla_ops : t_map -> string list -> (string * smtsort list * smtsort) list * string list
