(** A helper class for printing hierarchical data structures while traversing
    them using a visitor. *)

class visitor_pp : object
  method add : (Format.formatter -> unit) -> unit
  (** Take contents of this pretty-printer as a format, to be printed using
      `%t`. *)

  method add_str : string -> unit
  (** Convenience wrapper around the add method. *)

  method as_fmt : Format.formatter -> unit
  (** Add a non-recursive element to the formatter. The formatter is added to
      the current scope. *)

  method scope :
    ((Format.formatter -> unit) -> Format.formatter -> unit) ->
    (unit -> 'a) ->
    'a
  (** Start new scope for the formatter and print its contents after `f` is
      executed. *)

  method scope_str : 'a. string -> (unit -> 'a) -> 'a
  (** Simplified version od the `scope` method. *)
end

val pp_expr : Format.formatter -> Tlapm_lib.Expr.T.expr -> unit
val pp_hyp : Format.formatter -> Tlapm_lib.Expr.T.hyp -> unit
