(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)

(** Tokens *)
module type Tok = sig
  type token
    (** Type of tokens *)

  val bof : Loc.locus -> token
    (** token representing start of file *)

  val rep : token -> string
    (** String representation of tokens *)

  val locus : token -> Loc.locus
    (** Origin of the token *)

  val eq : token -> token -> bool
    (** Are the tokens equivalent? *)

  val pp_print_token : Format.formatter -> token -> unit
    (** For use in format strings *)
end

(** Precedence *)
module type Prec = sig
  type prec
    (** Abstract type of precedence *)

  val below : prec -> prec -> bool
    (** {!below} [p q] means that [p] is entirely below [q] *)

  val conflict : prec -> prec -> bool
    (** {!conflict} [p q] means that an unbracketed expression with
        two operators of precedence [p] and [q] respectively would be
        ambiguous. *)
end
