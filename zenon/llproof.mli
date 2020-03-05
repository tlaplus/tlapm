(*  Copyright 2003 INRIA  *)

open Expr;;

(* On utilise le type Expr.expr avec les restrictions suivantes:

  1. Emeta et Etau ne sont pas utilises.
  2. La distinction entre terme et proposition est respectee.
  3. Le predicat "=" a toujours deux arguments.

  Types:
   "?" -> wildcard -> "_"
   autre -> type specifie par l'utilisateur
*)


type binop =
  | And
  | Or
  | Imply
  | Equiv
  (* ... *)
;;

(*
  Format des regles:

  H1 ... Hn
  --------- regle
      C

  H1, ... Hn, C sont des listes de propositions

  Un noeud de preuve donne la conclusion (conc), la regle (rule), et
  les sous-noeuds (hyps = [hyp_1 ... hyp_n]).
  Le noeud est valide si conc contient tous les elements de C,
  et si, pour tout i, hyp_i est inclus dans conc + Hi

  informellement, une liste P1 ... Pn represente le sequent
       P1 ... Pn |- False
  ou encore la proposition  P1 -> ... -> Pn -> False

  Un arbre valide represente la preuve de la conclusion de sa racine.

  Notation: << t1=t2 >> denote << Eapp("=",[t1;t2]) >>
*)

type rule =
  | Rfalse
    (*
       ------ Rfalse
       Efalse

     ********************)

  | Rnottrue
    (*
       ----------- Rnottrue
       Enot(Etrue)

     ********************)

  | Raxiom of expr
    (*
       ---------- Raxiom (p)
       p, Enot(p)

     ********************)

  | Rcut of expr
    (*
       p     Enot(p)
       ------------- Rcut (p)


     ********************)

  | Rnoteq of expr
    (*
       ------------ Rnoteq (t)
       Enot (t = t)

     ********************)

  | Reqsym of expr * expr
    (*
       ------------ Reqsym (t, u)
       t = u, Enot (u = t)

     ********************)

  | Rnotnot of expr
    (*
            p
       -------------- Rnotnot p
       Enot (Enot(p))

     ********************)

  | Rconnect of binop * expr * expr
    (*
          p,q
       --------- Rconnect (And, p, q)
       Eand(p,q)

       p             q
       --------------- Rconnect (Or, p, q)
           Eor(p,q)

       Enot(p)          q
       ------------------ Rconnect (Imply, p, q)
          Eimply(p,q)

       Enot(p),Enot(q)    p,q
       ---------------------- Rconnect (Equiv, p, q)
            Eequiv(p,q)

     ********************)

  | Rnotconnect of binop * expr * expr
    (*
       Enot(p)       Enot(q)
       --------------------- Rnotconnect (And, p, q)
         Enot (Eand (p,q))

       Enot(p),Enot(q)
       ---------------- Rnotconnect (Or, p, q)
       Enot (Eor (p,q))

            p,Enot(q)
       ------------------- Rnotconnect (Imply, p, q)
       Enot (Eimply (p,q))

       Enot(p),q     p,Enot(q)
       ----------------------- Rnotconnect (Equiv, p, q)
          Enot (Eequiv,p,q))

     ********************)

  | Rex of expr * expr
    (*
         P{tau x.~P(x)}
       ----------------- Rex (Eex (x, ty, P{x}, _), tau x.~P(x))
       Eex (x, ty, P{x})

     ********************)

  | Rall of expr * expr    (* prop, term *)
    (*
              P{t}
       ------------------ Rall (Eall (x, ty, P{x}, _), t)
       Eall (x, ty, P{x})

     ********************)

  | Rnotex of expr * expr  (* prop, term *)
    (*
              Enot(P{t})
       ------------------------ Rnotex (Eex (x, ty, P{x}, _), t)
       Enot (Eex (x, ty, P{x}))

     *********************)

  | Rnotall of expr * expr
    (*
            Enot(P{tau(P)})
       ------------------------- Rnotall (Eall (x, ty, P{x}, _), tau(P))
       Enot (Eall (x, ty, P{x}))

     *********************)

  | Rpnotp of expr * expr
    (*
       Enot (t1 = u1)        ...        Enot (tn = un)
       ----------------------------------------------- Rx
       Eapp (p, [t1...tn]), Enot (Eapp (p, [u1...un]))

       Rx = Rpnotp (Eapp (p, [t1...tn]), Enot (Eapp (p, [u1...un])))

     ********************)

  | Rnotequal of expr * expr
    (*
       Enot (t1 = u1)           ...          Enot (tn = un)
       ---------------------------------------------------- Rx
       Enot ((Eapp (f, [t1...tn])) = (Eapp (f, [u1...un])))

       Rx = Rnotequal (Eapp (f, [t1...tn]), Eapp (f, [u1...un]))

     ********************)

  | RcongruenceLR of expr * expr * expr
    (*
           apply P b
       ------------------ Rcongruence (P, a, b)
         apply P a, a=b
    *)

  | RcongruenceRL of expr * expr * expr
    (*
           apply P b
       ------------------ Rcongruence (P, a, b)
         apply P a, b=a
    *)

  | Rdefinition of string * string * expr list * expr * string option
                   * expr * expr
    (*
        H
       --- Rdefinition (name, sym, args, body, recarg, C, H)
        C

       Si on peut passer de C a H en depliant la definition "name" de sym.
       La definition est sym(args) = body.
       recarg = None pour une definition non recursive.
       recarg = Some v pour une definition recursive avec decroissante sur v.

     ********************)

  | Rextension of string * string * expr list * expr list * expr list list
    (*
       H11...H1n   ...   Hp1...Hpq
       --------------------------- Rx
                 C1...Cn

       Rx = Rextension (ext, name, args, [C1...Cn],
                        [[H11...H1n] ... [Hp1...Hpq]])

       Ou name est le nom d'un lemme predefini tel que (name args) a le type:
       (H11 -> ... -> H1n -> False) -> ... -> (Hp1 -> ... -> Hpq -> False)
       -> (C1 -> ... -> Cn -> False)

       ext est le nom de l'extension qui doit gerer la traduction vers Coq,
       ou la chaine vide pour la traduction par defaut (application directe
       du lemme).

     ********************)

  | Rlemma of string * expr list
    (*
       ----------- Rlemma (name, args)
            C

       Si C est la conclusion de la preuve associee a "name" dans la
       liste de preuves.  Les arguments "args" correspondent aux
       parametres de "name".

     ********************)
;;

type prooftree = {
  conc : expr list;
  rule : rule;
  hyps : prooftree list;
};;

type lemma = {
  name : string;                  (* nom du lemme *)
  params : (string * expr) list;  (* (type, actual) *)
  proof : prooftree;              (* preuve *)
};;

type proof = lemma list;;

(* peephole optimiser for LL proofs *)
val optimise : proof -> proof;;

val iter : (prooftree -> unit) -> proof -> unit;;
