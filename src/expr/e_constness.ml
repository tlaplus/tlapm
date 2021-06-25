(*
 * expr/constness.ml --- detect constant operators
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property

open E_t

module Visit = E_visit


let isconst : bool pfuncs =
  Property.make ~uuid:"595aaaad-07ca-498b-8ebc-a473db6b0b27" "Expr.Constness.isconst"

let has_const x = Property.has x isconst
(*let is_const x = Property.get x isconst*)
let is_const x = try Property.get x isconst with
| Not_found -> false


class virtual const_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx e = match e.core with
    | Lambda (vss, le) ->
        let hs = List.map begin
          fun (v, shp) ->
            assign (Fresh (v, shp, Constant, Unbounded) @@ v) isconst true
        end vss in
        let scx = Visit.adjs scx hs in
        let le = self#expr scx le in
        let e = Lambda (vss, le) @@ e in
        (* Util.eprintf e *)
        (*   "const (%a) <-- %b@." *)
        (*   (Fmt.pp_print_expr (snd scx, Ctx.dot)) e *)
        (*   (Property.has le isconst) ; *)
        assign e isconst (is_const le)
    | Sequent sq ->
        let (_, sq) = super#sequent scx sq in
        let e = Sequent sq @@ e in
        let rec sq_const cx = match Deque.front cx with
          | None -> is_const sq.active
          | Some (h, cx) -> begin
              let hgood = match h.core with
                | Fresh (_, _, Constant, _) -> true
                | ( Defn ({core = Operator (_, e)}, _, _, _)
                  | Fact (e, _, _)
                  ) ->
                    is_const e
                | _ -> false
              in
              hgood && sq_const cx
            end
        in
        assign e isconst (sq_const sq.context)
    | _ ->
        let e = super#expr scx e in
        let cx = snd scx in
        let const = match e.core with
          | Ix n -> begin
              match Deque.nth ~backwards:true cx (n - 1) with
                | Some h -> begin match h.core with
                    | Defn ({core = Operator (_, op)}, _, _, _) ->
                        is_const op
                    | Fresh (_, _, Constant, _) ->
                        true
                    | _ ->
                        false
                  end
                | _ ->
                    Util.printf ~at:e "\n%s\n" (E_fmt.string_of_expr cx e);
                    Errors.bug ~at:e "Expr.Constness.propagate#expr: Ix"
            end
          |  Opaque _ ->
              true
          | ( Tquant _
            | Sub _
            | Tsub _
            | Fair _
            ) -> false
          | Internal b -> begin match b with
              | Builtin.Prime | Builtin.StrongPrime
              | Builtin.Leadsto | Builtin.ENABLED
              | Builtin.UNCHANGED | Builtin.Cdot
              | Builtin.Actplus | Builtin.Box _
              | Builtin.Diamond ->
                  false
              | _ ->
                  true
            end
          | Lambda (vss, e) ->
              Errors.bug ~at:e "Expr.Constness.propagate#expr: Lambda"
          | Sequent sq ->
              Errors.bug ~at:e "Expr.Constness.propagate#expr: Sequent"
          | Bang (e,_) -> (* TL: we ignore the selection for now *)
            is_const e
          | Apply (op, args) ->
              is_const op && List.for_all is_const args
          | Let (ds, e) -> begin
              let rec c_defns cx = function
                | [] -> is_const e
                | d :: ds -> begin
                    let dgood = match d.core with
                      | Operator (_, e) -> is_const e
                      | _ -> false
                    in
                    dgood &&
                      let h = Defn (d, User, Visible, Local) @@ d in
                      let h = assign h isconst true in
                      c_defns (Deque.snoc cx h) ds
                  end
              in
              c_defns cx ds
            end
          | ( String _
            | Num _
            | At _
            ) -> true
          | ( With (e, _)
            | Dot (e, _)
            | Parens (e, _)
            ) ->
              is_const e
          | ( Quant (_, bs, qe)
            | Fcn (bs, qe)
            | SetOf (qe, bs)
            ) -> begin
              let rec c_bounds cx = function
                | [] -> is_const qe
                | (v, k, bd) :: bs -> begin
                    let bdgood = match bd with
                      | Domain d -> is_const d
                      | _ -> true
                    in
                    bdgood &&
                      let h = Fresh (v, Shape_expr, Constant, Unbounded) @@ v in
                      let h = assign h isconst true in
                      c_bounds (Deque.snoc cx h) bs
                  end
              in
              c_bounds cx bs
            end
          | Choose (v, None, e) ->
              is_const e
          | ( Choose (v, Some d, e)
            | SetSt (v, d, e)
            ) ->
              is_const d && is_const e
          | If (e, f, g) ->
              is_const e && is_const f && is_const g
          | ( List (_, es)
            | Tuple es
            | Product es
            | SetEnum es
            ) -> List.for_all is_const es
          | FcnApp (f, es) ->
              is_const f && List.for_all is_const es
          | ( Rect fs
            | Record fs
            ) -> List.for_all (fun (_, e) -> is_const e) fs
          | Arrow (e, f) ->
              is_const e && is_const f
          | Except (e, xs) ->
              let c_exspec (tr, re) =
                List.for_all begin function
                  | Except_dot _ -> true
                  | Except_apply e -> is_const e
                end tr && is_const re
              in
              is_const e && List.for_all c_exspec xs
          | Case (arms, oth) ->
              List.for_all begin
                fun (p, e) -> is_const p && is_const e
              end arms
              && begin
                match oth with
                  | None -> true
                  | Some e -> is_const e
              end
        in
        assign e isconst const

  method hyp scx h = if (has_const h) then (scx,h) else super#hyp scx h
  method pform scx p = if (has_const p) then p else super#pform scx p
  method defn scx p = if (has_const p) then p else super#defn scx p
end
