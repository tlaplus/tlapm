open Property
open Util
open E_t


class level_comparison : object
    method compare : ctx -> ctx -> expr -> expr -> bool

    method expr : ctx -> ctx -> expr -> expr -> bool
    method exprs : ctx -> ctx -> expr list -> expr list -> bool

    method bounds_cx : ctx -> bounds -> ctx
    method bounds : ctx -> ctx -> bounds -> bounds -> bool
    method bound : ctx -> ctx -> bound -> bound -> bool
    method bdom : ctx -> ctx -> bound_domain -> bound_domain -> bool

    method opt_expr : ctx -> ctx -> expr option -> expr option -> bool

    method defns_cx : ctx -> defn list -> ctx
    method defns : ctx -> ctx -> defn list -> defn list -> bool
    method defn : ctx -> ctx -> defn -> defn -> bool

    method sequent : ctx -> ctx -> sequent -> sequent -> bool
    method context : ctx -> ctx -> ctx -> ctx -> bool
    method hyps_cx : ctx -> ctx -> ctx
    method hyp : ctx -> ctx -> hyp -> hyp -> bool
    method hyp_cx : ctx -> hyp -> ctx

    method instance : ctx -> ctx -> instance -> instance -> bool
    method sub : ctx -> ctx ->
        (hint * expr) list -> (hint * expr) list -> bool
    method sel : ctx -> ctx -> sel -> sel -> bool
end


val check_level_change : ctx -> expr -> expr
