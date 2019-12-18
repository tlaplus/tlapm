(*
 * axiom.mli --- TLA+ axioms
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(** Repertory for TLA+'s axioms, stated as {!Expr.T.expr} expressions.

    Name conventions:
      - 'varX'  variant of axiom X;
      - 'ext'   indicates an extensionality axiom;
      - 'def'   for predicate/operator definitions;
      - 'car'   for destructor characterization.
*)

open Expr.T


(** {3 Pure Set Theory} *)

val set_ext : expr
(** [\A x, y : (\A z : z \in x <=> z \in y) => x = y] *)

val setext_witness : string
val var_set_ext : expr
(** [\A x, y : (setext_witness(x, y) \in x <=> setext_witness(x, y) \in y)
                  => x = y]
*)

val subseteq_def : expr
(** [\A x, y : x \subseteq y <=> \A z : z \in x => z \in y] *)

val empty_def : expr
(** [\A x : ~ (x \in {})] *)

val var_empty_def : expr
(** [\A x : x \notin {}] *)

val enum_def : int -> expr
(** [\A a1, .., an, x : x \in { a1, .., an } <=> x = a1 \/ .. \/ x = an]

    [enum_def 0] redirects to [empty_def].
*)

val subset_def : expr
(** [\A a, x : x \in SUBSET a <=> \A y : y \in x => y \in a] *)

val var_subset_def : expr
(** [\A a, x : x \in SUBSET a <=> x \subseteq a] *)

val union_def : expr
(** [\A a, x : x \in UNION a <=> \E y : y \in a /\ x \in y] *)

val cup_def : expr
(** [\A a, b, x : x \in a \cup b <=> x \in a \/ x \in b] *)

val cap_def : expr
(** [\A a, b, x : x \in a \cap b <=> x \in a /\ x \in b] *)

val setminus_def : expr
(** [\A a, b, x : x \in a \ b <=> x \in a /\ ~ (x \in b)] *)

val var_setminus_def : expr
(** [\A a, b, x : x \in a \ b <=> x \in a /\ x \notin b] *)

val setst_def : int -> expr
(** [ASSUME NEW P(_, .., _)
     PROVE  \A a1, .., an, s, x :
              x \in { y \in s : P(a1, .., an, y) } <=>
                x \in s /\ P(a1, .., an, x)]
*)

val setof_def : int -> int -> expr
(** [ASSUME NEW F(_, .., _)
     PROVE  \A a1, .., am, s1, .., sn, y :
              y \in { F(a1, .., am, x1, .., xn) : x1 \in s1, .., xn \in sn } <=>
                \E x1, .., xn : /\ x1 \in s1 /\ .. /\ xn \in sn
                                /\ y = F(a1, .., am, x1, .., xn)]
*)


(** {3 Products} *)

val tuple_ext : int -> expr
(** [\A a1, .., an, b1, .., bn :
        << a1, .., an >> = << b1, .., bn >> => a1 = b1 /\ .. /\ an = bn]

    [tuple_ext 0] and [tuple_ext 1] raise [Invalid_argument].
*)

val unit_def : expr
(** [\A x : x \in Unit <=> x = unit] *)

val product_def : int -> expr
(** [\A a1, .., an, x :
        x \in a1 \X .. \X an <=>
          \E y1, .., yn : /\ y1 \in a1 /\ .. /\ yn \in an
                          /\ x = << y1, .., yn >>]

    [product_def 0] redirects to [unit_def].
    [product_def 1] raises [Invalid_argument]: the unary product of
    a set [a] is just [a].
*)

val var_product_def : int -> expr
(** [\A a1, .., an, x :
        x \in a1 \X .. \X an <=>
          /\ x[1] \in a1 /\ .. /\ x[n] \in an
          /\ x = << x[n], .., x[n] >>]

    [var_product_def 0] redirects to [unit_def].
    [var_product_def 1] raises [Invalid_argument]: the unary product of
    a set [a] is just [a].
*)

val tupdom_car : int -> expr
(** [\A a1, .., an : DOMAIN << a1, .., an >> = 1..n]

    [tupdom_car 0] and [tupdom_car 1] raise [Invalid_argument].
*)

val tupapp_car : int -> expr
(** [\A a1, .., an, i : i \in 1..n => << a1, .., an >>[i] = ai]

    [tupapp_car 0] and [tupapp_car 1] raise [Invalid_argument].
*)


(** {3 Functions} *)

val fun_ext : int -> expr
(** [\A a1, .., an, b, f, g :
        f \in [ a1 \X .. \X an -> b ] /\ g \in [ a1 \X .. \X an -> b ] =>
            (\A x1, .., xn : x1 \in a1 /\ .. /\ xn \in an =>
                    f[x1, .., xn] = g[x1, .., xn]) => f = g]

    [fun_ext 0] raises [Invalid_argument].
*)

val arrow_def : int -> expr
(** [\A a1, .., an, b, f :
        f \in [ a1 \X .. \X an -> b ] <=>
            /\ DOMAIN f = a1 \X .. \X an
            /\ \A x1, .., xn : x1 \in a1 /\ .. /\ xn \in an =>
                    f[x1, .., xn] \in b]

    [arrow_def 0] raises [Invalid_argument].
*)

val domain_car : int -> int -> expr
(** [ASSUME NEW F(_, .., _)
     PROVE  \A a1, .., am, s1, .., sn :
              DOMAIN [ x1 \in s1, .., xn \in sn |-> F(a1, .., am, x1, .., xn) ] =
                s1 \X .. \X sn]

    [domain_car m 0] raises [Invalid_argument].
*)

val fcnapp_car : int -> int -> expr
(** [ASSUME NEW F(_, .., _)
     PROVE  \A a1, .., am, s1, .., sn, x1, .., xn :
              x1 \in s1 /\ .. /\ xn \in sn =>
                [ y1 \in s1, .., yn \in sn |-> F(a1, .., am, y1, .., yn) ][x1, .., xn] =
                    F(a1, .., am, x1, .., xn)]

    [fcnapp_car m 0] raises [Invalid_argument].
*)


(** {3 Records} *)

val record_ext : string list -> expr
(** [\A a1, .., an, r, s :
        r \in [ s1 : a1, .., sn : an ] /\ s \in [ s1 : a1, .., sn : an ] =>
            (/\ r.s1 = s.s1
             ..
             /\ r.sn = s.sn) =>
                r = s]

    [rec_ext []] raises [Invalid_argument].
*)

val rect_def : string list -> expr
(** [\A a1, .., an, r :
        r \in [ s1 : a1, .., sn : an ] <=>
            /\ DOMAIN r = { "s1", .., "sn" }
            /\ r.s1 \in a1
            ..
            /\ r.sn \in an]

    [rect_def []] raises [Invalid_argument].
*)

val recdom_car : string list -> expr
(** [\A a1, .., an :
        DOMAIN [ s1 |-> a1, .., sn |-> an ] = { "s1", .., "sn" }}]
    
    [recdom_car []] raises [Invalid_argument].
*)

val recdot_car : string list -> expr
(** [\A a1, .., an :
        /\ [ s1 |-> a1, .., sn |-> an ].s1 = a1}
        ..
        /\ [ s1 |-> a1, .., sn |-> an ].sn = an}]
    
    [recdot_car []] raises [Invalid_argument].
*)


(** {3 Sequences} *)

(* TODO *)


