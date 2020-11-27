(*
 * encode/reduce.mli --- eliminate higher-order
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Expr.T
open Type.T

(** Reduction eliminates HO features from TLA+ expressions.  This particular
    implementation support expressions in standardized form, for which most
    constructs are reduced to applications.

    The effect of reduction is to transform application with HO arguments to
    new applications with only FO arguments.  This is done by defining new
    instances of the operators, specialized with the relevant HO arguments.
    Some adjustments are needed to account for local variables present inside
    the HO arguments--they become new FO arguments.

    Example.
    [ASSUME NEW SetSt(s, P(_)) == { x \in s : P(x) },
            NEW S,
            \A c : SetSt(S, LAMBDA x : x # c) # {}
     PROVE TRUE]

    When [do_reduce] is called on the application of [SetSt], the local context
    contains the variable [c].  This variable becomes a parameter of the new
    operator, so that the declaration can be put above the local context.

    Result:
    [ASSUME NEW SetSt(s, P(_)) == { x \in s : P(x) },
            NEW S,
            NEW SetSt_R(S, c) == SetSt(S, LAMBDA x : x # c),
            \A c : SetSt_R(S, c) # {}
     PROVE TRUE]

    An additional task of reduction is to instantiate axioms schemas with
    the right HO parameters.  In the previous example, one would need to add
    the axiom:
    [\A S, c, x : x \in SetSt_R(S, c) <=> x \in S /\ x # c]

    Axioms attached to an operator must be marked using the property
    {!Encode.Axiomatize.axm_ptrs_prop}.
*)


(* NOTE Signatures and comments are here for documentation.
 * Use {!main} only. *)

(** A context partitioned into a global and a local part.  The [int] parameter
    is always set as the depth of the local context.  A value of [0] means that
    the context is only global.
*)
type ctx = int Expr.Visit.scx

(** Transform an application with HO arguments to an application without.
    Call: [do_reduce ctx op ty2 es]
    @param ctx is the context of the application
    @param op is the operator
    @param ty2 is the type of the operator
    @param es are the arguments
    @return h the declaration of a new operator [op']
    @return es' the new arguments for [op']

    This function will be called when encountering an application
    [Apply(op, es)] with [op : ty2] and [ty2] is a second-order type.

    Rather than returning a replacement expression, the function returns
    a declaration for the replacement operator, [op'], and replacement
    arguments [es'].  The reason for this is that [op'] cannot be referenced
    (with a De Bruijn variable) in the context of the original expr, because
    its declaration is not present.

    The hypothesis [h] is a definition; the definiens is adjusted to the
    same context as the original expr.  Therefore the new hyp should be
    inserted in place of the fact the original expression was found, while
    the rest of the sequent is shifted.
*)
val do_reduce : ctx -> expr -> ty_sch -> expr list -> hyp * expr list

(** [instantiate sq i e] returns a sequent obtained from [sq] by instantiating
    the ith quantifier with [e].  This is especially intended for higher-order
    instantiations.
    @raise Invalid_arg when [i] is wrong somehow
*)
val instantiate : sequent -> int -> expr -> sequent
val instantiate_expr : expr -> int -> expr -> expr


(** Eliminate second-order arguments in applications, by inserting new
    declarations for the instantiated operators.
*)
val main : sequent -> sequent

