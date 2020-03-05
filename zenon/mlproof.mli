(*  Copyright 2003 INRIA  *)

open Expr;;

type rule =
  | Close of expr               (* p, -p  /  (.)                [p]*)
  | Close_refl of string * expr (* -r(a,a)  /  (.)              [r a]*)
  | Close_sym of string * expr * expr
                                (* r(a,b), -r(b,a)  /  (.)      [r a b]*)
  | False                       (* false  /  (.)                []*)
  | NotTrue                     (* -true  /  (.)                []*)
  | NotNot of expr              (* --p  /  p                    [p]*)
  | And of expr * expr          (* p/\q  /  p, q                [p q]*)
  | NotOr of expr * expr        (* -(p\/q)  /  -p, -q           [p q]*)
  | NotImpl of expr * expr      (*-(p=>q)  /  p, -q             [p q]*)
  | NotAll of expr              (*-A.p  /  -p(t(-p))            [-A.p]*)
  | NotAllEx of expr            (*-A.p  /  -p(t(-p))            [-A.p]*)
  | Ex of expr                  (* E.p  /  p(t(p))              [E.p]*)
  | All of expr * expr          (* A.p  /  p(a)                 [A.p a]*)
  | NotEx of expr * expr        (* -E.p  /  -p(a)               [-E.p a]*)
  | Or of expr * expr           (* p\/q  /  p | q               [p q]*)
  | Impl of expr * expr         (* p=>q  /  -p | q              [p q]*)
  | NotAnd of expr * expr       (* -(p/\q)  /  -p | -q          [p q]*)
  | Equiv of expr * expr        (* p<=>q  /  -p, -q | p, q      [p q]*)
  | NotEquiv of expr * expr     (* -(p<=>q)  /  -p, q | p, -q   [p q]*)
  | P_NotP of expr * expr
      (* P(a0, .. an), -P(b0, .. bn)  /  a0!=b0 | .. an!=bn     [P(..) -P(..)]*)
  | P_NotP_sym of string * expr * expr
      (* r(a,b), -r(c,d)  /  b!=c  |  a!=d                      [r r(.) -r(.)]*)
  | NotEqual of expr * expr
      (* F(a0, .. an)!=F(b0, .. bn)  /  a0!=b0 | .. an!=bn      [F(a..) F(b.)]*)
  | Definition of definition * expr * expr
      (* folded  /  unfolded                                    [def fld unf]*)
  | ConjTree of expr            (* p1/\p2/\..  /  p1, p2, ..    [conj]*)
  | DisjTree of expr            (* p1\/p2\/..  /  p1 | p2 | ..  [disj]*)
  | AllPartial of expr * string * int
                                (* Ax.p(x)  /  Axyz.p(s(xyz))   [Axpx s ar]*)
  | NotExPartial of expr * string * int
                                (* -Ex.p(x)  /  -Exyz.p(s(xyz)) [-Expx s ar]*)
  | Refl of string * expr * expr
                                (* -r(a,b)  /  a!=b             [r a b]*)
  | Trans of expr * expr
      (* r(a,b),-r(c,d)  /  c!=a,-r(c,a) | b!=d,-r(b,d)         [rab -rcd]*)
  | Trans_sym of expr * expr
      (* r(a,b),-r(c,d)  /  d!=a,-r(d,a) | b!=c,-r(b,c)         [rab -rcd]*)
  | TransEq of expr * expr * expr
      (* a=b,-r(c,d)  /  c!=a,-r(c,a) | -r(c,a),-r(b,d) | b!=d,-r(b,d)
                                                                [a b -rcd]*)
  | TransEq2 of expr * expr * expr
      (* a=b,-r(c,d)  /  c!=b,-r(c,b) | -r(c,b),-r(a,d) | a!=d,-r(a,d)
                                                                [a b -rcd]*)
  | TransEq_sym of expr * expr * expr
      (* a=b,-r(c,d)  /  d!=a,-r(d,a) | -r(d,a),-r(b,c) | b!=c,-r(b,c)
                                                                [a b -rcd]*)

  | Cut of expr                 (*   / p | -p                   [p]*)
  | CongruenceLR of expr * expr * expr
                                (* p[a],a=b / p[b]              [p a b]*)
  | CongruenceRL of expr * expr * expr
                                (* p[a],b=a / p[b]              [p a b]*)
  | Miniscope of expr * expr * expr list
      (* $scope (f, t, v1, ...) / f[v1] | ... | t != v1, ... , f[t]
                                                                [f t v1 ...] *)

  | Ext of string * string * expr list
                                (* ... [extension, rule, arguments]*)
;;

type proof = {
  mlconc : expr list;      (* conclusion *)
  mlrule : rule;           (* rule *)
  mlhyps : proof array;    (* proof branches *)
  mutable mlrefc : int;    (* reference count *)
};;

val size : proof -> int;;

val iter : (proof -> unit) -> proof -> unit;;

val make_node : expr list -> rule -> expr list list -> proof list -> proof;;

val make_cl : expr -> proof;;
val make_clr : string -> expr -> proof;;
val make_cls : string -> expr -> expr -> proof;;
val make_f : proof;;
val make_nt : proof;;
val make_nn : expr -> proof -> proof;;
val make_and : expr -> expr -> proof -> proof;;
val make_nor : expr -> expr -> proof -> proof;;
val make_nimpl : expr -> expr -> proof -> proof;;
val make_nall : expr -> proof -> proof;;
val make_ex : expr -> proof -> proof;;
val make_all : expr -> expr -> proof -> proof;;
val make_nex : expr -> expr -> proof -> proof;;
val make_or : expr -> expr -> proof -> proof -> proof;;
val make_impl : expr -> expr -> proof -> proof -> proof;;
val make_nand : expr -> expr -> proof -> proof -> proof;;
val make_eqv : expr -> expr -> proof -> proof -> proof;;
val make_neqv : expr -> expr -> proof -> proof -> proof;;
val make_pnp : expr -> expr -> proof list -> proof;;
val make_pnps : string -> expr -> expr -> proof -> proof -> proof;;
val make_neql : expr -> expr -> proof list -> proof;;
val make_conglr : expr -> expr -> expr -> proof -> proof;;
val make_congrl : expr -> expr -> expr -> proof -> proof;;
val make_def : definition -> expr -> expr -> proof -> proof;;

val make_cut : expr -> proof -> proof -> proof;;

(*
  These are not provided because they are derived rules

val make_ctree : expr -> expr list -> proof -> proof;;
val make_dtree : expr -> expr list -> proof list -> proof;;
val make_allp : expr -> string -> int -> proof -> proof;;
val make_nexp : expr -> string -> int -> proof -> proof;;
val make_refl : string -> expr -> expr -> proof -> proof;;
val make_trans :
  string -> expr -> expr -> expr -> expr -> proof -> proof -> proof
;;
val make_transs :
   string -> expr -> expr -> expr -> expr -> proof -> proof -> proof
;;
val make_transeq :
  string -> expr -> expr -> expr -> expr -> proof -> proof -> proof
;;
val make_transeqs :
  string -> expr -> expr -> expr -> expr -> proof -> proof -> proof
;;
val make_miniscope : expr -> expr -> expr list -> proof list -> proof;;
*)
