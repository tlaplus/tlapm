(* Normalization of expressions.

Copyright (C) 2013  INRIA and Microsoft Corporation
*)
open Ext
open Format
open Tla_parser
open Property

open E_t
module B = Builtin

let ( @@ ) core e = E_levels.newcache (core @@ e)

let rec tuple_flatten e = match e.core with
  | Tuple es ->
      List.concat (List.map tuple_flatten es)
  | _ -> [e]

let unchanged e =
  let dest = e in
  Apply (Internal B.Eq @@ dest, [ Apply (Internal B.Prime @@ dest, [e]) @@ dest ; e ]) @@ dest

let rewrite_unch e =
  let dest = e in
  match tuple_flatten e with
    | [] -> Internal B.TRUE @@ dest
    | [e] -> unchanged e
    | es -> List (And, List.map unchanged es) @@ dest

include (E_visit : sig
           type 's scx = 's * hyp Deque.dq
           val adj  : 's scx -> hyp -> 's scx
         end)

let expand_leadsto =
  let visitor = object (self : 'self)
    inherit [unit] E_visit.map as super
    method expr scx e = match e.core with
      | Apply ({ core = Internal B.Leadsto }, [f1;f2]) ->
          Apply (Internal (B.Box true) @@ e, [
            Apply (Internal B.Implies @@ e, [
              self#expr scx f1;
                Apply (Internal B.Diamond @@ e, [
                  self#expr scx f2]) @@ e
                ]
              ) @@ e
            ]) @@ e
      | _ -> super#expr scx e
  end in
  fun scx e ->
    visitor#expr scx e

let expand_fairness =
  let visitor = object (self : 'self)
    inherit [unit] E_visit.map as super
    method expr scx e =
      let sub_dia f a = Sub (Dia, a,f) @@ a in
      let tsub_dia f a = Tsub (Dia, a,f) @@ a in
      let put_box p = Apply (Internal (B.Box true) @@ p, [p]) @@ p in
      let put_dia p = Apply (Internal (B.Diamond) @@ p, [p]) @@ p in
      let rhs f a = put_box (tsub_dia f a) in
      let en f a = Apply (Internal B.ENABLED @@ a, [sub_dia f a]) @@ a in
      let imp p1 p2 = Apply (Internal B.Implies @@ p1, [p1;p2]) @@ p1 in
      match e.core with
      | Fair (Weak, f, a) -> imp (put_dia (put_box (en f a))) (rhs f a)
      | Fair (Strong, f, a) -> imp (put_box (put_dia (en f a))) (rhs f a)
      | _ -> super#expr scx e
  end in
  fun scx e ->
    visitor#expr scx e

let expand_unchanged =
  let visitor = object (self : 'self)
    inherit [unit] E_visit.map as super
    method expr scx e = match e.core with
      | Apply ({ core = Internal B.UNCHANGED }, [e]) ->
          rewrite_unch e
      | _ -> super#expr scx e
  end in
  fun scx e ->
    visitor#expr scx e

let expand_action =
  let visitor = object (self : 'self)
    inherit [unit] E_visit.map as super
    method expr scx e =
      let dest = e in
      match e.core with
        | Sub (Box, e, v) ->
            let e = self#expr scx e in
            let v = self#expr scx v in
            Apply begin
              Internal B.Disj @@ dest,
              [ e ; Apply (Internal B.UNCHANGED @@ dest, [v]) @@ dest ]
            end @@ dest
        | Tsub (Box, e, v) ->
            let e = self#expr scx e in
            let v = self#expr scx v in
            Apply (Internal (B.Box true) @@ dest, [
              Apply begin
              Internal B.Disj @@ dest,
              [ e ; Apply (Internal B.UNCHANGED @@ dest, [v]) @@ dest ]
              end @@ dest]) @@ dest
        | Sub (Dia, e, v) ->
            let e = self#expr scx e in
            let v = self#expr scx v in
            Apply begin
              Internal B.Conj @@ dest,
              [ e ;
                Apply begin
                  Internal B.Neg @@ dest,
                  [Apply (Internal B.UNCHANGED @@ dest, [v]) @@ dest]
                end @@ dest ;
              ]
            end @@ dest
        | Tsub (Dia, e, v) ->
            let e = self#expr scx e in
            let v = self#expr scx v in
            Apply (Internal B.Diamond @@ dest, [
            Apply begin
              Internal B.Conj @@ dest,
              [ e ;
                Apply begin
                  Internal B.Neg @@ dest,
                  [Apply (Internal B.UNCHANGED @@ dest, [v]) @@ dest]
                end @@ dest ;
              ]
            end @@ dest]) @@ dest
        | _ -> super#expr scx e
  end in
  fun scx e -> visitor#expr scx e


let%test_module _ = (module struct
  let sexp_of_string = Sexplib.Std.sexp_of_string
  let compare_string = Base.compare_string

  let parse_expr = Tla_parser.P.use (E_parser.expr true);;
  let nullctx = (Deque.empty, Ctx.dot);;

  let create_expression str =
    let (flex, _) = Alexer.lex_string str in
    match Tla_parser.P.run parse_expr ~init:Tla_parser.init ~source:flex with
      | Some e -> e
      | None -> failwith "cannot parse test string"

  let prn_exp exp =
        Tla_parser.Fu.pp_print_minimal
        Format.str_formatter (E_fmt.fmt_expr nullctx exp);
        Format.flush_str_formatter ()

  let prn_str str = str

  let%test_unit "t1" =
    let test_string = "WF_f(A)" in
    let test_case = create_expression test_string in
    let target_string = "<>[]ENABLED<<A>>_f => []<><<A>>_f" in
    let target_case = create_expression target_string in
      [%test_eq: string] (prn_exp target_case) (prn_exp (expand_fairness ((),Deque.empty) test_case))

  let%test_unit "t2" =
    let test_string = "SF_f(A)" in
    let test_case = create_expression test_string in
    let target_string = "[]<>ENABLED<<A>>_f => []<><<A>>_f" in
    let target_case = create_expression target_string in
      [%test_eq: string] (prn_exp target_case) (prn_exp (expand_fairness ((),Deque.empty) test_case))

end)
