(*
 * axiom.ml --- TLA+ axioms
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

open Ext
open Property
open Expr.T

module B = Builtin


(** {3 Helpers} *)

let app b es = Apply (Internal b %% [], es)

let una b e1    = app b [ e1 ]
let ifx b e1 e2 = app b [ e1 ; e2 ]

let quant q xs e = Quant (q, List.map (fun x -> (x %% [], Constant, No_domain)) xs, e)
let all xs e = quant Forall xs e
let exi xs e = quant Exists xs e

let gen x n = List.init n (fun i -> x ^ string_of_int (i + 1))
(** [gen "x" n] = [ "x1" ; .. ; "xn" ] *)

let ixi ?(shift=0) n = List.init n (fun i -> Ix (shift + n - i) %% [])
(** [ixi n]          = [ Ix n ; .. ; Ix 2 ; Ix 1 ]
    [ixi ~shift:s n] = [ Ix (s+n) ; .. ; Ix (s+2) ; Ix (s+1) ]
*)


(** {3 Pure Set Theory} *)

(** [\A x, y : (\A z : z \in x <=> z \in y) => x = y] *)
let set_ext =
  all [ "x" ; "y" ] (
    ifx B.Implies (
      all ["z"] (
        ifx B.Equiv (
          ifx B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
        ) (
          ifx B.Mem (Ix 1 %% []) (Ix 2 %% []) %% []
        ) %% []
      ) %% []
    ) (
      ifx B.Eq (Ix 2 %% []) (Ix 1 %% []) %% []
    ) %% []
  ) %% []

let setext_witness = "TLA__setext_witness"

(** [\A x, y : (setext_witness(x, y) \in x <=> setext_witness(x, y) \in y)
                  => x = y]
*)
let var_set_ext =
  all [ "x" ; "y" ] (
    ifx B.Implies (
      ifx B.Equiv (
        ifx B.Mem (
          Apply (Opaque setext_witness %% [], [ Ix 2 %% [] ; Ix 1 %% [] ]) %% []
        ) (
          Ix 2 %% []
        ) %% []
      ) (
        ifx B.Mem (
          Apply (Opaque setext_witness %% [], [ Ix 2 %% [] ; Ix 1 %% [] ]) %% []
        ) (
          Ix 1 %% []
        ) %% []
      ) %% []
    ) (
      ifx B.Eq (Ix 2 %% []) (Ix 1 %% []) %% []
    ) %% []
  ) %% []

(** [\A x, y : x \subseteq y <=> \A z : z \in x => z \in y] *)
let subseteq_def =
  all [ "x" ; "y" ] (
    ifx B.Equiv (
      ifx B.Subseteq (Ix 2 %% []) (Ix 1 %% []) %% []
    ) (
      all [ "z" ] (
        ifx B.Implies (
          ifx B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
        ) (
          ifx B.Mem (Ix 1 %% []) (Ix 2 %% []) %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

(** [\A x : ~ (x \in {})] *)
let empty_def =
  all [ "x" ] (
    una B.Neg (
      ifx B.Mem (Ix 1 %% []) (SetEnum [] %% []) %% []
    ) %% []
  ) %% []

(** [\A x : x \notin {}] *)
let var_empty_def =
  all [ "x" ] (
    ifx B.Notmem (Ix 1 %% []) (SetEnum [] %% []) %% []
  ) %% []

(** [\A a1, .., an, x : x \in { a1, .., an } <=> x = a1 \/ .. \/ x = an] *)
let enum_def n =
  if n = 0 then
    empty_def
  else
    all (gen "a" n @ [ "x" ]) (
      ifx B.Equiv (
        ifx B.Mem (
          Ix 1 %% []
        ) (
          SetEnum (ixi ~shift:1 n) %% []
        ) %% []
      ) (
        List (Or, List.init n begin fun i ->
          ifx B.Eq (Ix 1 %% []) (Ix (n - i + 1) %% []) %% []
        end) %% []
      ) %% []
    ) %% []

(** [\A a, x : x \in SUBSET a <=> \A y : y \in x => y \in a] *)
let subset_def =
  all [ "a" ; "x" ] (
    ifx B.Equiv (
      ifx B.Mem (Ix 1 %% []) (una B.SUBSET (Ix 2 %% []) %% []) %% []
    ) (
      all [ "y" ] (
        ifx B.Implies (
          ifx B.Mem (Ix 1 %% []) (Ix 2 %% []) %% []
        ) (
          ifx B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

(** [\A a, x : x \in SUBSET a <=> x \subseteq a] *)
let var_subset_def =
  all [ "a" ; "x" ] (
    ifx B.Equiv (
      ifx B.Mem (Ix 1 %% []) (una B.SUBSET (Ix 2 %% []) %% []) %% []
    ) (
      ifx B.Subseteq (Ix 1 %% []) (Ix 2 %% []) %% []
    ) %% []
  ) %% []

(** [\A a, x : x \in UNION a <=> \E y : y \in a /\ x \in y] *)
let union_def =
  all [ "a" ; "x" ] (
    ifx B.Equiv (
      ifx B.Mem (Ix 1 %% []) (una B.UNION (Ix 2 %% []) %% []) %% []
    ) (
      exi [ "y" ] (
        ifx B.Conj (
          ifx B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
        ) (
          ifx B.Mem (Ix 2 %% []) (Ix 1 %% []) %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

(** [\A a, b, x : x \in a \cup b <=> x \in a \/ x \in b] *)
let cup_def =
  all [ "a" ; "b" ; "x" ] (
    ifx B.Equiv (
      ifx B.Mem (
        Ix 1 %% []
      ) (
        ifx B.Cup (Ix 3 %% []) (Ix 2 %% []) %% []
      ) %% []
    ) (
      ifx B.Disj (
        ifx B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
      ) (
        ifx B.Mem (Ix 1 %% []) (Ix 2 %% []) %% []
      ) %% []
    ) %% []
  ) %% []

(** [\A a, b, x : x \in a \cap b <=> x \in a /\ x \in b] *)
let cap_def =
  all [ "a" ; "b" ; "x" ] (
    ifx B.Equiv (
      ifx B.Mem (
        Ix 1 %% []
      ) (
        ifx B.Cap (Ix 3 %% []) (Ix 2 %% []) %% []
      ) %% []
    ) (
      ifx B.Conj (
        ifx B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
      ) (
        ifx B.Mem (Ix 1 %% []) (Ix 2 %% []) %% []
      ) %% []
    ) %% []
  ) %% []

(** [\A a, b, x : x \in a \ b <=> x \in a /\ ~ (x \in b)] *)
let setminus_def =
  all [ "a" ; "b" ; "x" ] (
    ifx B.Equiv (
      ifx B.Mem (
        Ix 1 %% []
      ) (
        ifx B.Setminus (Ix 3 %% []) (Ix 2 %% []) %% []
      ) %% []
    ) (
      ifx B.Conj (
        ifx B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
      ) (
        una B.Neg (
          ifx B.Mem (Ix 1 %% []) (Ix 2 %% []) %% []
        ) %% []
      ) %% []
    ) %% []
  ) %% []

(** [\A a, b, x : x \in a \ b <=> x \in a /\ x \notin b] *)
let var_setminus_def =
  all [ "a" ; "b" ; "x" ] (
    ifx B.Equiv (
      ifx B.Mem (
        Ix 1 %% []
      ) (
        ifx B.Cap (Ix 3 %% []) (Ix 2 %% []) %% []
      ) %% []
    ) (
      ifx B.Conj (
        ifx B.Mem (Ix 1 %% []) (Ix 3 %% []) %% []
      ) (
        ifx B.Notmem (Ix 1 %% []) (Ix 2 %% []) %% []
      ) %% []
    ) %% []
  ) %% []

(** [ASSUME NEW P(_, .., _)
     PROVE  \A a1, .., an, s, x :
              x \in { y \in s : P(a1, .., an, y) } <=>
                x \in s /\ P(a1, .., an, x)]
*)
let setst_def n =
  Sequent {
    context = Deque.of_list [
      let shp = if n = 0 then Shape_expr else Shape_op n in
      Fresh ("P" %% [], shp, Constant, Unbounded) %% []
    ]
  ; active =
      all (gen "a" n @ [ "s" ; "x" ]) (
        ifx B.Equiv (
          ifx B.Mem (
            Ix 1 %% []
          ) (
            SetSt ("y" %% [], Ix 2 %% [],
              Apply (Ix (n + 3) %% [], ixi ~shift:4 n @ [ Ix 1 %% [] ]) %% []
            ) %% []
          ) %% []
        ) (
          ifx B.Conj (
            ifx B.Mem (Ix 1 %% []) (Ix 2 %% []) %% []
          ) (
            Apply (Ix (n + 3) %% [], ixi ~shift:2 n @ [ Ix 1 %% [] ]) %% []
          ) %% []
        ) %% []
      ) %% []
  } %% []

(** [ASSUME NEW F(_, .., _)
     PROVE  \A a1, .., am, s1, .., sn, y :
              y \in { F(a1, .., am, x1, .., xn) : x1 \in s1, .., xn \in sn } <=>
                \E x1, .., xn : /\ x1 \in s1 /\ .. /\ xn \in sn
                                /\ y = F(a1, .., am, x1, .., xn)]
*)
let setof_def m n =
  Sequent {
    context = Deque.of_list [
      let shp = if m + n = 0 then Shape_expr else Shape_op (m + n) in
      Fresh ("F" %% [], shp, Constant, Unbounded) %% []
    ]
  ; active =
      all (gen "a" m @ gen "s" n @ [ "y" ]) (
        ifx B.Equiv (
          ifx B.Mem (
            Ix 1 %% []
          ) (
            SetOf (
              Apply (Ix (m + n + 2) %% [], ixi ~shift:(2*n + 1) m @ ixi n) %% [],
              List.init n begin fun i ->
                let x = "x" ^ string_of_int (i + 1) in
                (x %% [], Constant, Domain (Ix (n - i) %% []))
              end
            ) %% []
          ) %% []
        ) (
          exi (gen "x" n) (
            List (And,
              List.init n begin fun i ->
                ifx B.Mem (Ix (n - i) %% []) (Ix (2*n - i) %% []) %% []
              end
              @ [ ifx B.Eq (
                    Ix n %% []
                  ) (
                    Apply (
                      Ix (m + 2*n + 2) %% [],
                      ixi ~shift:(2*n + 1) m @ ixi n
                    ) %% []
                  ) %% []
              ]
            ) %% []
          ) %% []
        ) %% []
      ) %% []
  } %% []


(** {3 Products} *)

(** [\A a1, .., an, b1, .., bn :
        << a1, .., an >> = << b1, .., bn >> => a1 = b1 /\ .. /\ an = bn]
*)
let tuple_ext n =
  if n = 0 then
    raise (Invalid_argument "tuple_ext 0")
  else if n = 1 then
    raise (Invalid_argument "tuple_ext 1")
  else
    all (gen "a" n @ gen "b" n) (
      ifx B.Implies (
        ifx B.Eq (
          Tuple (ixi ~shift:n n) %% []
        ) (
          Tuple (ixi n) %% []
        ) %% []
      ) (
        List (And, List.init n begin fun i ->
          ifx B.Mem (Ix (2*n - i) %% []) (Ix (n - i) %% []) %% []
        end) %% []
      ) %% []
    ) %% []

(** [\A x : x \in Unit <=> x = unit] *)
let unit_def =
  all [ "x" ] (
    ifx B.Equiv (
      ifx B.Mem (Ix 1 %% []) (Product [] %% []) %% []
    ) (
      ifx B.Eq (Ix 1 %% []) (Tuple [] %% []) %% []
    ) %% []
  ) %% []

(** [\A a1, .., an, x :
        x \in a1 \X .. \X an <=>
          \E y1, .., yn : /\ y1 \in a1 /\ .. /\ yn \in an
                          /\ x = << y1, .., yn >>]
*)
let product_def n =
  if n = 0 then
    unit_def
  else if n = 1 then
    raise (Invalid_argument "product_def 1")
  else
    all (gen "a" n @ [ "x" ]) (
      ifx B.Equiv (
        ifx B.Mem (
          Ix 1 %% []
        ) (
          Product (ixi ~shift:1 n) %% []
        ) %% []
      ) (
        exi (gen "y" n) (
          List (And,
            List.init n begin fun i ->
              ifx B.Mem (Ix (n - i) %% []) (Ix (2*n - i) %% []) %% []
            end
            @ [
              ifx B.Eq (
                Ix n %% []
              ) (
                Tuple (ixi n) %% []
              ) %% []
            ]
          ) %% []
        ) %% []
      ) %% []
    ) %% []

(** [\A a1, .., an, x :
        x \in a1 \X .. \X an <=>
          /\ x[1] \in a1 /\ .. /\ x[n] \in an
          /\ x = << x[n], .., x[n] >>]
*)
let var_product_def n =
  if n = 0 then
    unit_def
  else if n = 1 then
    raise (Invalid_argument "var_product_def 1")
  else
    all (gen "a" n @ [ "x" ]) (
      ifx B.Equiv (
        ifx B.Mem (
          Ix 1 %% []
        ) (
          Product (ixi ~shift:1 n) %% []
        ) %% []
      ) (
        List (And,
          List.init n begin fun i ->
            ifx B.Mem (
              FcnApp (
                Ix 1 %% [],
                [ Num (string_of_int (i + 1), "") %% [] ]
              ) %% []
            ) (
              Ix (n - i) %% []
            ) %% []
          end
          @ [
            ifx B.Eq (
              Ix 1 %% []
            ) (
              Tuple (List.init n begin fun i ->
                FcnApp (
                  Ix 1 %% [],
                  [ Num (string_of_int (i + 1), "") %% [] ]
                ) %% []
              end) %% []
            ) %% []
          ]
        ) %% []
      ) %% []
    ) %% []

(** [\A a1, .., an : DOMAIN << a1, .., an >> = 1..n] *)
let tupdom_car n =
  if n = 0 then
    raise (Invalid_argument "tupdom_car 0")
  else if n = 1 then
    raise (Invalid_argument "tupdom_car 1")
  else
    all (gen "a" n) (
      ifx B.Eq (
        una B.DOMAIN (
          Tuple (ixi n) %% []
        ) %% []
      ) (
        ifx B.Range (
          Num (string_of_int 1, "") %% []
        ) (
          Num (string_of_int n, "") %% []
        ) %% []
      ) %% []
    ) %% []

(** [\A a1, .., an : /\ << a1, .., an >>[1] = a1 
                     ..
                     /\ << a1, .., an >>[n] = an]
*)
let tupapp_car n =
  if n = 0 then
    raise (Invalid_argument "tupapp_car 0")
  else if n = 1 then
    raise (Invalid_argument "tupapp_car 1")
  else
    all (gen "a" n) (
      List (And, List.init n begin fun i ->
        ifx B.Eq (
          FcnApp (
            Tuple (ixi n) %% [],
            [ Num (string_of_int (i + 1), "") %% [] ]
          ) %% []
        ) (
          Ix (n - i) %% []
        ) %% []
      end) %% []
    ) %% []


(** {3 Functions} *)

(** [\A a1, .., an, b, f, g :
        f \in [ a1 \X .. \X an -> b ] /\ g \in [ a1 \X .. \X an -> b ] =>
            (\A x1, .., xn : x1 \in a1 /\ .. /\ xn \in an =>
                    f[x1, .., xn] = g[x1, .., xn]) => f = g
*)
let fun_ext n =
  if n = 0 then
    raise (Invalid_argument "fun_ext 0")
  else
    all (gen "a" n @ [ "b" ; "f" ; "g" ]) (
      ifx B.Implies (
        let arrow_set =
          Arrow (
            begin if n = 1 then
              Ix 4 %% []
            else
              Product (ixi ~shift:3 n) %% []
            end,
            Ix 3 %% []
          )
        in
        ifx B.Conj (
          ifx B.Mem (Ix 2 %% []) (arrow_set %% []) %% []
        ) (
          ifx B.Mem (Ix 1 %% []) (arrow_set %% []) %% []
        ) %% []
      ) (
        ifx B.Implies (
          all (gen "x" n) (
            ifx B.Implies (
              List (And, List.init n begin fun i ->
                ifx B.Mem (
                  Ix (n - i) %% []
                ) (
                  Ix (2*n + 2 - i) %% []
                ) %% []
              end) %% []
            ) (
              ifx B.Eq (
                FcnApp (Ix (n + 2) %% [], ixi n) %% []
              ) (
                FcnApp (Ix n %% [], ixi n) %% []
              ) %% []
            ) %% []
          ) %% []
        ) (
          ifx B.Eq (Ix 2 %% []) (Ix 1 %% []) %% []
        ) %% []
      ) %% []
    ) %% []

(** [\A a1, .., an, b, f : f \in [ a1 \X .. \X an -> b ] <=>
                            /\ DOMAIN f = a1 \X .. \X an
                            /\ \A x1, .., xn : x1 \in a1 /\ .. /\ xn \in an =>
                                    f[x1, .., xn] \in b
*)
let arrow_def n =
  if n = 0 then
    raise (Invalid_argument "arrow_def m 0")
  else
    all (gen "a" n @ [ "b" ; "f" ]) (
      let domain =
        if n = 1 then
          Ix 3
        else
          Product (ixi ~shift:2 n)
      in
      ifx B.Equiv (
        ifx B.Mem (Ix 1 %% []) (Arrow (domain %% [], Ix 2 %% []) %% []) %% []
      ) (
        List (And, [
          ifx B.Eq (
            una B.DOMAIN (Ix 1 %% []) %% []
          ) (
            domain %% []
          ) %% []
        ; all (gen "x" n) (
            ifx B.Implies (
              List (And, List.init n begin fun i ->
                ifx B.Mem (Ix (n - i) %% []) (Ix (2*n + 2 - i) %% []) %% []
              end) %% []
            ) (
              ifx B.Mem (
                FcnApp (Ix n %% [], ixi n) %% []
              ) (
                Ix 2 %% []
              ) %% []
            ) %% []
          ) %% []
        ]) %% []
      ) %% []
    ) %% []

(** [ASSUME NEW F(_, .., _)
     PROVE  \A a1, .., am, s1, .., sn :
              DOMAIN [ x1 \in s1, .., xn \in sn |-> F(a1, .., am, x1, .., xn) ] =
                s1 \X .. \X sn]
*)
let domain_car m n =
  if n = 0 then
    raise (Invalid_argument "domain_car m 0")
  else
    Sequent {
      context = Deque.of_list [
        let shp = Shape_op (m + n) in
        Fresh ("F" %% [], shp, Constant, Unbounded) %% []
      ]
    ; active =
        all (gen "a" m @ gen "s" n) (
          ifx B.Eq (
            una B.DOMAIN (
              Fcn (
                List.init n begin fun i ->
                  let x = "x" ^ string_of_int (i + 1) in
                  (x %% [], Constant, Domain (Ix (n - i) %% []))
                end,
                Apply (Ix n %% [], ixi ~shift:(2*n) m @ ixi n) %% []
              ) %% []
            ) %% []
          ) (
            if n = 1 then
              Ix 1 %% []
            else
              Product (ixi n) %% []
          ) %% []
        ) %% []
    } %% []

(** [ASSUME NEW F(_, .., _)
     PROVE  \A a1, .., am, s1, .., sn, x1, .., xn :
              x1 \in s1 /\ .. /\ xn \in sn =>
                [ y1 \in s1, .., yn \in sn |-> F(a1, .., an, y1, .., yn) ][x1, .., xn] =
                    F(a1, .., am, x1, .., xn)]
*)
let fcnapp_car m n =
  if n = 0 then
    raise (Invalid_argument "fcnapp_car m 0")
  else
    Sequent {
      context = Deque.of_list [
        let shp = Shape_op (m + n) in
        Fresh ("F" %% [], shp, Constant, Unbounded) %% []
      ]
    ; active =
        all (gen "a" m @ gen "s" n @ gen "x" n) (
          ifx B.Implies (
            List (And, List.init n begin fun i ->
              ifx B.Mem (Ix (n - i) %% []) (Ix (2*n - i) %% []) %% []
            end) %% []
          ) (
            ifx B.Eq (
              FcnApp (
                Fcn (
                  List.init n begin fun i ->
                    let x = "x" ^ string_of_int (i + 1) in
                    (x %% [], Constant, Domain (Ix (2*n - i) %% []))
                  end,
                  Apply (Ix (m + 3*n) %% [], ixi ~shift:(3*n) m @ ixi n) %% []
                ) %% [],
                ixi n
              ) %% []
            ) (
              Apply (Ix (m + 2*n) %% [], ixi ~shift:(2*n) m @ ixi n) %% []
            ) %% []
          ) %% []
        ) %% []
    } %% []


(** {3 Records} *)

(** [\A a1, .., an, r, s :
        r \in [ s1 : a1, .., sn : an ] /\ s \in [ s1 : a1, .., sn : an ] =>
            (/\ r.s1 = s.s1
             ..
             /\ r.sn = s.sn) =>
                r = s]

    [rec_ext []] raises [Invalid_argument].
*)
let record_ext ss =
  let n = List.length ss in
  if n = 0 then
    raise (Invalid_argument "record_ext []")
  else
    all (gen "a" n @ [ "r" ; "s" ]) (
      ifx B.Implies (
        ifx B.Conj (
          ifx B.Mem (
            Ix 2 %% []
          ) (
            Rect (List.mapi begin fun i s ->
              (s, Ix (n + 2 - i) %% [])
            end ss) %% []
          ) %% []
        ) (
          ifx B.Mem (
            Ix 1 %% []
          ) (
            Rect (List.mapi begin fun i s ->
              (s, Ix (n + 2 - i) %% [])
            end ss) %% []
          ) %% []
        ) %% []
      ) (
        ifx B.Implies (
          List (And, List.mapi begin fun i s ->
            ifx B.Eq (
              Dot (Ix 2 %% [], s) %% []
            ) (
              Dot (Ix 1 %% [], s) %% []
            ) %% []
          end ss) %% []
        ) (
          ifx B.Eq (Ix 2 %% []) (Ix 1 %% []) %% []
        ) %% []
      ) %% []
    ) %% []

(** [\A a1, .., an, r :
        r \in [ s1 : a1, .., sn : an ] <=>
            /\ DOMAIN r = { "s1", .., "sn" }
            /\ r.s1 \in a1
            ..
            /\ r.sn \in an]

    [rect_def []] raises [Invalid_argument].
*)
let rect_def ss =
  let n = List.length ss in
  if n = 0 then
    raise (Invalid_argument "rect_def []")
  else
    all (gen "a" n @ [ "r" ]) (
      ifx B.Equiv (
        ifx B.Mem (
          Ix 1 %% []
        ) (
          Rect (List.mapi begin fun i s ->
            (s, Ix (n - i) %% [])
          end ss) %% []
        ) %% []
      ) (
        List (And, [
            ifx B.Eq (
              una B.DOMAIN (Ix 1 %% []) %% []
            ) (
              SetEnum (List.map begin fun s ->
                String s %% []
              end ss) %% []
            ) %% []
          ] @
          List.mapi begin fun i s ->
            ifx B.Mem (
              Dot (Ix 1 %% [], s) %% []
            ) (
              Ix (n - i) %% []
            ) %% []
          end ss
        ) %% []
      ) %% []
    ) %% []

(** [\A a1, .., an :
        DOMAIN [ s1 |-> a1, .., sn |-> an ] = { "s1", .., "sn" }}]
    
    [recdom_car []] raises [Invalid_argument].
*)
let recdom_car ss =
  let n = List.length ss in
  if n = 0 then
    raise (Invalid_argument "recdom_car []")
  else
    all (gen "a" n) (
      ifx B.Eq (
        una B.DOMAIN (
          Record (List.mapi begin fun i s ->
            (s, Ix (n - i) %% [])
          end ss) %% []
        ) %% []
      ) (
        SetEnum (List.map begin fun s ->
          String s %% []
        end ss) %% []
      ) %% []
    ) %% []

(** [\A a1, .., an :
        /\ [ s1 |-> a1, .., sn |-> an ].s1 = a1}
        ..
        /\ [ s1 |-> a1, .., sn |-> an ].sn = an}]
    
    [recdot_car []] raises [Invalid_argument].
*)
let recdot_car ss =
  let n = List.length ss in
  if n = 0 then
    raise (Invalid_argument "recdot_car []")
  else
    all (gen "a" n) (
      List (And, List.mapi begin fun i s ->
        ifx B.Eq (
          Dot (
            Record (List.mapi begin fun i s ->
              (s, Ix (n - i) %% [])
            end ss) %% [],
            s
          ) %% []
        ) (
          Ix (n - i) %% []
        ) %% []
      end ss) %% []
    ) %% []


(** {3 Sequences} *)

(* TODO *)


