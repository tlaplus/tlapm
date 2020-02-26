(*
 * smt/rewrite_arith.ml --- Rewrite arithmetic expressions.
 *
 * Author: Hern\'an Vanzetto <hernan.vanzetto@inria.fr>
 *
 * Copyright (C) 2011-2020  INRIA and Microsoft Corporation
 *)

open Ext
open Property

open Expr.T
open Expr.Subst
open Expr.Visit

open Printf
open List

module B = Builtin
module T = Typ_t
module Smt = Smtcommons

let is_Int scx e = T.is_int (snd scx) e

(** Rewriter for arithmetic expressions *)
class rw = object (self : 'self)
  inherit [unit] Expr.Visit.map as super
  method hyp scx h = match h.core with
    | Defn (_, _, Hidden, _) (** ignore these cases *)
    | Fact (_, Hidden, _) ->
      (adj scx h, h)
    | _ ->
      super#hyp scx h
  method expr scx e =
    (* Util.eprintf "rw arith: %a" (Expr.Fmt.pp_print_expr (snd scx, Ctx.dot)) e ; *)
    let mk x = { e with core = x } in
    let build ex = match ex.core with a -> a |> mk in                           (** mantains e's original properties, especially the isconc property *)
    let apply op es = Apply (Internal op |> mk, es) |> mk in
    let leq x y = apply B.Lteq [x ; y] in
    let plus x y = apply B.Plus [x ; y] in
    let minus x y = apply B.Minus [x ; y] in
    let zero = Num ("0","") |> mk in
    let str_is_int x = try int_of_string x = int_of_string x with _ -> false in
    (* let string_of_float' x = Str.replace_first (Str.regexp "^\\(.*\\)\\.$") "\\1" (string_of_float x) in *)
    match e.core with
    | Apply ({core = Internal op} as o, [x ; y]) ->
      let x = self#expr scx x in
      let y = self#expr scx y in
      let is_neg n = n.[0] = '-' in
      let mk_num n = Num (string_of_int n,"") |> mk in
      let abs n = if is_neg n then Num (String.sub n 1 ((String.length n) - 1),"") |> mk else mk_num (int_of_string n) in
      begin match op, x.core, y.core with
        | (B.Plus | B.Minus), _, Num ("0","") when is_Int scx x -> build x
        | B.Plus, Num ("0",""), _ when is_Int scx y -> build y
        | B.Minus, Num ("0",""), _ when is_Int scx y -> Apply (Internal B.Uminus |> mk, [y]) |> mk

        (** Trivial arithmetic rules, no context needed *)
        | B.Plus, Num (x,""), Num (y,"") when str_is_int x && str_is_int y ->
          mk_num ((int_of_string x) + (int_of_string y))
        | B.Minus, Num (x,""), Num (y,"") when str_is_int x && str_is_int y ->
          let n = (int_of_string x) - (int_of_string y) in
          if n < 0 then Apply (Internal B.Uminus |> mk, [mk_num (n * -1)]) |> mk else mk_num n
        | B.Times, Num (x,""), Num (y,"") when str_is_int x && str_is_int y ->
          mk_num ((int_of_string x) * (int_of_string y))
        (* | B.Quotient,  Num (x,""), Num (y,"") when str_is_int x && str_is_int y && int_of_string y > 0 ->
                                                                                   mk_num ((int_of_string x) / (int_of_string y)) (* integer division *)
           | B.Remainder, Num (x,""), Num (y,"") when str_is_int x && str_is_int y && int_of_string y > 0 ->
                                                                                   mk_num ((int_of_string x) mod (int_of_string y))
           | B.Ratio,     Num (x,""), Num (y,"") when str_is_int x && str_is_int y && int_of_string y <> 0 ->
                                                                                   Num (string_of_float' ((float_of_string x) /. (float_of_string y)),"") |> mk
           | B.Exp,       Num (x,""), Num (y,"") when str_is_int x && str_is_int y -> Num (string_of_float' ((float_of_string x) ** (float_of_string y)),"") |> mk *)

        | B.Minus, _, _ when is_Int scx x && is_Int scx y && Expr.Eq.expr x y ->
          zero
        | B.Lteq, _, _  when is_Int scx x && is_Int scx y && Expr.Eq.expr x y ->
          Internal B.TRUE |> mk

        (** algebraic manipulation *)
        | B.Lteq, Apply ({core = Internal B.Plus}, [x ; y]), Apply ({core = Internal B.Plus}, [z ; w])
          when for_all (is_Int scx) [x;y;z;w] && Expr.Eq.expr x z ->
          leq y w
        | B.Lteq, Apply ({core = Internal B.Plus}, [x ; y]), Apply ({core = Internal B.Plus}, [z ; w])
          when for_all (is_Int scx) [x;y;z;w] && Expr.Eq.expr y w ->
          leq x z
        | B.Lteq, Apply ({core = Internal B.Plus}, [x ; y]), Apply ({core = Internal B.Plus}, [z ; w])
          when for_all (is_Int scx) [x;y;z;w] && Expr.Eq.expr x w ->
          leq y z
        | B.Lteq, Apply ({core = Internal B.Plus}, [x ; y]), Apply ({core = Internal B.Plus}, [z ; w])
          when for_all (is_Int scx) [x;y;z;w] && Expr.Eq.expr y z ->
          leq x w

        (** algebraic manipulation, recursive *)
        | (B.Lteq | B.Gteq), _, Apply ({core = Internal B.Minus}, [z ; w])
          when for_all (is_Int scx) [x;z;w] ->
          Apply (o, [plus x w ; z]) @@ e |> self#expr scx
        | (B.Lteq | B.Gteq), Apply ({core = Internal B.Minus}, [z ; w]), _
          when for_all (is_Int scx) [y;z;w] ->
          Apply (o, [z ; plus y w]) @@ e |> self#expr scx

        | B.Eq, _, Apply ({core = Internal B.Minus}, [z ; w])
          when for_all (is_Int scx) [x;z;w] ->
          Apply (o, [plus x w ; z]) @@ e |> self#expr scx
        | B.Eq, Apply ({core = Internal B.Minus}, [z ; w]), _
          when for_all (is_Int scx) [z;w;y] ->
          Apply (o, [z ; plus y w]) @@ e |> self#expr scx

        (* | B.Plus, x, y ->
            let uminus1 e = match e.core with
            | Apply ({core = Internal B.Uminus}, [e]) -> e
            | Num (n,"") when is_neg n -> abs n
            | Num (n,"") -> Num ("-"^n,"") |> mk
            | _ -> Apply (Internal B.Uminus, [e]) |> mk
            in
            let uminus es = map uminus1 es in
            let rec to_add e =
              match e.core with
              | Apply ({core = Internal o}, [x ; y]) ->
                  begin match o, x.core, y.core with
                  | B.Plus, x, y  -> to_add x @ to_add y
                  | B.Minus, x, y -> to_add x @ uminus (to_add y)
                  | _ -> [e]
                  end
              | _ -> [e]
            in

            let xs = to_add e in
            let nums,xs = partition (fun e -> match e.core with Num _ -> true | _ -> false) xs in
            let xs = order xs in
            let xs = simplify xs in
            to_expr xs *)

        | B.Minus, Apply ({core = Internal B.Plus},  [x ; z]), _ when for_all (is_Int scx) [x;y;z] && Expr.Eq.expr x y -> self#expr scx z
        | B.Minus, Apply ({core = Internal B.Plus},  [z ; x]), _ when for_all (is_Int scx) [x;y;z] && Expr.Eq.expr x y -> self#expr scx z
        | B.Plus,  Apply ({core = Internal B.Minus}, [x ; z]), _ when for_all (is_Int scx) [x;y;z] && Expr.Eq.expr z y -> self#expr scx x
        | B.Plus,  _, Apply ({core = Internal B.Minus}, [y ; z]) when for_all (is_Int scx) [x;y;z] && Expr.Eq.expr x z -> self#expr scx y

        (** number simpl *)
        | B.Plus,  Apply ({core = Internal B.Plus}, [ex ; ({core = Num _} as x)]), Num _
          when is_Int scx ex ->
          self#expr scx (plus ex (self#expr scx (plus x y)))
        | B.Plus,  Apply ({core = Internal B.Plus}, [({core = Num _} as x) ; ex]), Num _
          when is_Int scx ex ->
          self#expr scx (plus ex (self#expr scx (plus x y)))
        | B.Plus,  Num _, Apply ({core = Internal B.Plus},  [ex ; ({core = Num _} as y)])
          when is_Int scx ex ->
          self#expr scx (plus ex (self#expr scx (plus x y)))
        | B.Plus,  Num _, Apply ({core = Internal B.Plus},  [({core = Num _} as y) ; ex])
          when is_Int scx ex ->
          self#expr scx (plus ex (self#expr scx (plus x y)))

        | B.Plus,  Apply ({core = Internal B.Minus}, [ex ; ({core = Num _} as x)]), Num _
          when is_Int scx ex -> self#expr scx (plus ex (self#expr scx (minus y x)))
        | B.Plus,  Apply ({core = Internal B.Minus}, [({core = Num _} as x) ; ex]), Num _
          when is_Int scx ex -> self#expr scx (minus (self#expr scx (plus y x)) ex)
        | B.Minus, Apply ({core = Internal B.Plus},  [ex ; ({core = Num _} as x)]), Num _
          when is_Int scx ex -> self#expr scx (plus ex (self#expr scx (minus x y)))
        | B.Minus, Apply ({core = Internal B.Plus},  [({core = Num _} as x) ; ex]), Num _
          when is_Int scx ex -> self#expr scx (plus ex (self#expr scx (minus x y)))
        | B.Minus, Apply ({core = Internal B.Minus}, [ex ; ({core = Num _} as x)]), Num _
          when is_Int scx ex -> self#expr scx (minus ex (self#expr scx (plus x y)))
        | B.Minus, Apply ({core = Internal B.Minus}, [({core = Num _} as x) ; ex]), Num _
          when is_Int scx ex -> self#expr scx (minus (self#expr scx (minus x y)) ex)

        (* | B.Plus,  Num _, Apply ({core = Internal B.Minus}, [ex ; ({core = Num _} as y)]) -> self#expr scx (plus ex (self#expr scx (minus x y))) *)
        (* | B.Plus,  Num _, Apply ({core = Internal B.Minus}, [({core = Num _} as y) ; ex]) -> self#expr scx (minus (self#expr scx (plus x y)) ex) *)
        (* | B.Minus, Num _, Apply ({core = Internal B.Plus},  [ex ; ({core = Num _} as y)]) *)
        (* | B.Minus, Num _, Apply ({core = Internal B.Plus},  [({core = Num _} as y) ; ex]) -> self#expr scx (minus (self#expr scx (minus x y)) ex) *)
        (* | B.Minus, Num _, Apply ({core = Internal B.Minus}, [ex ; ({core = Num _} as y)]) -> self#expr scx (minus (self#expr scx (plus x y)) ex) *)
        (* | B.Minus, Num _, Apply ({core = Internal B.Minus}, [({core = Num _} as y) ; ex]) -> self#expr scx (plus ex (self#expr scx (minus x y))) *)

        (** Algebraic manipulation *)
        | B.Plus,  _, Apply ({core = Internal B.Minus}, [y ; z]) when is_Int scx x && is_Int scx y && is_Int scx z -> self#expr scx (minus (plus x y) z)
        | B.Plus,  Apply ({core = Internal B.Minus}, [x ; z]), _ when is_Int scx x && is_Int scx y && is_Int scx z -> self#expr scx (minus (plus x y) z)
        | B.Minus, _, Apply ({core = Internal B.Plus},  [y ; z]) when is_Int scx x && is_Int scx y && is_Int scx z -> self#expr scx (minus (minus x y) z)
        | B.Minus, _, Apply ({core = Internal B.Minus}, [y ; z]) when is_Int scx x && is_Int scx y && is_Int scx z -> self#expr scx (minus (plus x z) y)

        (* | B.Plus,  Apply ({core = Internal B.Minus}, [ex ; x]), _ -> self#expr scx (plus ex (minus y x)) *)
        (* | B.Minus, Apply ({core = Internal B.Plus},  [ex ; x]), _ -> self#expr scx (plus ex (self#expr scx (minus x y))) *)
        (* | B.Minus, Apply ({core = Internal B.Minus}, [ex ; x]), _ -> self#expr scx (minus ex (plus x y)) *)

        | B.Plus, _, Num (n,"")  when is_Int scx x && is_neg n -> self#expr scx (minus x (abs n) )
        | B.Plus, Num (n,""), _  when is_Int scx y && is_neg n -> self#expr scx (minus y (abs n) )
        | B.Minus, _, Num (n,"") when is_Int scx x && is_neg n -> self#expr scx (plus  x (abs n) )

        (* | B.Mem, Apply ({core = Internal B.Plus}, [a ; b]), (Internal B.Int | Internal B.Nat) ->
            self#expr scx (List (And, [mem a y ; mem b y]) |> mk)
           | B.Mem, Apply ({core = Internal (B.Minus | B.Times | B.Exp) }, [a ; b]), Internal B.Int ->
            self#expr scx (List (And, [mem a y ; mem b y]) |> mk) *)

        | _ -> Apply (o, [x ; y]) |> mk
      end
    (** The next two rules are not recommended. Better keep the original structure of the PO. *)
    (* | Apply ({core = Internal B.Neg}, [{core = Apply ({core = Internal B.Lteq}, [x ; y])}]) -> lt y x |> self#expr scx *)
    (* | Apply ({core = Internal B.Neg}, [{core = Apply ({core = Internal B.Lt},   [x ; y])}]) -> leq y x |> self#expr scx *)
    | _ ->
      super#expr scx e
end
