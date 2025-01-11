module LspT := Lsp.Types

module Position : sig
  type t [@@deriving show]

  val compare : t -> t -> int
end

type t [@@deriving show]

val from : t -> Position.t
val till : t -> Position.t
val line_from : t -> int
val line_till : t -> int
val as_lsp_range : t -> LspT.Range.t
val of_lsp_range : LspT.Range.t -> t
val of_string_opt : string -> t option
val of_locus : Tlapm_lib.Loc.locus -> t option
val of_locus_opt : Tlapm_lib.Loc.locus option -> t option
val of_locus_must : Tlapm_lib.Loc.locus -> t
val of_wrapped : 'a Tlapm_lib.Property.wrapped -> t option
val of_wrapped_must : 'a Tlapm_lib.Property.wrapped -> t
val of_points : Position.t -> Position.t -> t
val of_ints : lf:int -> cf:int -> lt:int -> ct:int -> t
val of_lines : int -> int -> t
val of_unknown : t
val of_all : t
val join : t -> t -> t
val string_of_range : t -> string
val string_of_pos : Position.t -> string
val compare : t -> t -> int
val before : Position.t -> t -> bool
val intersect : t -> t -> bool
val lines_intersect : t -> t -> bool
val line_covered : t -> Position.t -> bool
val lines_covered : t -> t -> bool
val lines_covered_or_all : t -> t list -> t
val first_diff_pos : string -> string -> Position.t
