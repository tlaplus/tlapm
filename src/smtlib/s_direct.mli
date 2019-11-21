(*
 * smtlib/direct.mli -- untyped encoding
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Util

open S_t
open S_symbs

(** The context of the expression being read. [hx] and [cx] follow the
    conventions of {!Expr.Fmt}. [lcx] is an initial segment of [cx], it
    corresponds to variables that are bound locally. [mem] is the set of
    subterms that are memorized for the encoding of higher-order expressions.
*)
type scx =
  { hx  : hyp Deque.dq
  ; cx  : int Ctx.t
  }

val bump  : scx -> scx
val adj   : scx -> symbol -> scx * string
val adjs  : scx -> symbol list -> scx * string list


(** Store terms to retrieve later; used for encoding higher-order constructs,
    to build axiom schemes.
*)
module Store : sig
  (* FIXME: make applicative *)
  type key
  val to_int : key -> int

  (** A term is stored along with a set of variables, which correspond to
      parameters in an axiom scheme. Usually these are a subset of the term's
      free variables.
  *)
  type elt = SmbSet.t * term

  (** [mk_key] always return a new key. *)
  val mk_key : elt -> key

  (** Retrieve the element previously stored. *)
  val get : key -> elt
end


type direct_req =
  | Core of core_smb_t        (** Core theory *)
  | Ints of ints_smb_t        (** Ints theory *)
  | Sets of sets_smb_t        (** Set theory *)
  | Bools of bools_smb_t      (** Boolean elements *)
  | Strings of strings_smb_t  (** String elements *)
  | UInts of uints_smb_t      (** Internal int elements *)
  | Funs of funs_smb_t        (** Function elements *)
  | Tuples of tuples_smb_t    (** Tuple elements *)
  | Recs of recs_smb_t        (** Record elements *)

  | New of symbol * int       (** First-order symbols *)

  (* Higher-order constructs *)
  | CompSet of symbol * Store.key
  | SubsSet of symbol list * Store.key
  | Fun of symbol list * Store.key
  | Epsilon of symbol * Store.key


module DDeps : Deps with type req = direct_req
module DManager : S with type req = direct_req


(** The encoding function recursively traverses expressions in a sequent.

    The layout is taken from {!Expr.Visit}, but it couldn't be implemented
    as a visitor object because te encoding on expressions must return terms.

    [enc_expr] takes a boolean parameter [expect_bool]. If set to [true], the
    resulting SMT expressions will be of type [Bool], else [U].

    [enc_lexpr] is used on the leftmost expressions in an [Apply]-term. It
    returns the symbol of the operand, and the signature of that operand
    (for this encoding the only sorts are Bool and U).
*)

type bsig = bool list * bool

val enc_expr    : ?expect_bool:bool -> scx -> theory -> expr         -> theory * term
val enc_lexpr   :                      scx -> theory -> expr         -> theory * symbol * bsig
val enc_sequent :                      scx -> theory -> sequent      -> theory * scx
val enc_hyps    :                      scx -> theory -> hyp Deque.dq -> theory * scx
val enc_hyp     :                      scx -> theory -> hyp          -> theory * scx
val enc_defns   :                      scx -> theory -> defn list    -> theory * scx
val enc_defn    :                      scx -> theory -> defn         -> theory * scx


(** Main encoding function *)
val encode_direct : sequent -> theory

