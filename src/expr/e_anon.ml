(*
 * expr/anon.ml --- expressions (anonymization)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

open Property
open E_t
open E_subst

module Elab = E_elab;;
module Visit = E_visit;;
module Deref = E_deref;;
module Eq = E_eq;;

let ( |> ) x f = f x

let hyp_is_named what h = match h.core with
  | Fresh (nm, _, _, _)
  | Flex nm
  | Defn ({core = Operator (nm, _) | Instance (nm, _)
                  | Bpragma(nm,_,_) | Recursive (nm, _)},
          _, _, _)
  -> nm.core = what
  | Fact (_, _, _) ->
      what = "_"

let standard_form ~cx ~dep ~wd op args = match wd with
  | Builtin ->
      if args = [] then
        (app_expr (shift dep) op).core @@ op
      else
        normalize ~cx:cx (app_expr (shift dep) op) args @@ op
  | _ ->
      if args = [] then
        Ix dep @@ op
      else
        Apply (Ix dep @@ op, args) @@ op


class anon_sg = object (self : 'self)
  inherit [string list] Visit.map as super

  method expr scx e =
    match e.core with
    | Bang ({core = Apply ({core = Opaque op}, args)}, sels) -> begin
        let sels = List.map (self#sel scx) sels in
        let args = List.map (self#expr scx) args in
        let scx = ([], snd scx) in
        (* check the operator without the "use <1>1 in proof of <1>1" warning *)
        let rec check (pfx, pargs) sels is_inst = begin
          match Deque.find ~backwards:true (snd scx) (hyp_is_named pfx) with
            | None -> begin match sels with
                | Sel_lab (sfx, sargs) :: sels ->
                    let sargs = List.map (self#expr scx) sargs in
                    check (pfx ^ "!" ^ sfx, pargs @ sargs) sels true
(* a enlever *) | (Sel_num n)::sels ->  Util.eprintf ~at:e
                      "Operator \"%s\" not found" pfx ;
                    Errors.set e (Printf.sprintf "Operator \"%s\" not found" pfx);
                    failwith "Expr.Anon: 1NUM"
                | (Sel_down)::sels ->  Util.eprintf ~at:e
                      "Operator \"%s\" not found" pfx ;
                    Errors.set e (Printf.sprintf "Operator \"%s\" not found" pfx);
                    failwith "Expr.Anon: 1DOWN"
                | (Sel_at)::sels ->  Util.eprintf ~at:e
                      "Operator \"%s\" not found" pfx ;
                    Errors.set e (Printf.sprintf "Operator \"%s\" not found" pfx);
                    failwith "Expr.Anon: 1AT"
                | (Sel_inst _)::sels ->  Util.eprintf ~at:e
                      "Operator \"%s\" not found" pfx ;
                    Errors.set e (Printf.sprintf "Operator \"%s\" not found" pfx);
                    failwith "Expr.Anon: 1INST"
                | [] -> Errors.set e (Printf.sprintf "Operator \"%s\" not found" pfx);
                    failwith "Expr.Anon: 1EMPTY"
                | _ ->
                    Util.eprintf ~at:e
                      "Operator \"%s\" not found" pfx ;
                    Errors.set e (Printf.sprintf "Operator \"%s\" not found" pfx);
                    failwith "Expr.Anon: 1"
              end
            | Some (dep, {core = Defn ({core = Operator (_, op)}, wd, _, _)}) ->
                begin match sels with
                  | [] when is_inst -> begin
                      let ix = Ix (dep + 1) @@ e in
                      match pargs with
                        | [] -> ix
                        | pargs ->
                            standard_form ~cx:(snd scx) ~dep:(dep + 1) ~wd:wd
                              (op.core @@ e) pargs
                    end
                  | _ -> begin
                      let op = app_expr (shift (dep + 1)) op in
                      let op = Util.set_locus op (Util.get_locus e) in
                      let se = Deref.resolve_bang (snd scx) op pargs sels in
                      if Deref.is_badexp se then begin
                        Util.eprintf ~at:e "Could not resolve subexpression reference" ;
                        Errors.set e (Printf.sprintf "Could not resolve subexpression reference");
                        failwith "Expr.Anon: 2"
                      end ;
                      Util.set_locus se (Util.get_locus e)
                    end
                end
            | Some _ ->
                Util.eprintf ~at:e "invalid subexpression reference" ;
                 Errors.set e (Printf.sprintf "invalid subexpression reference");
                 failwith "Expr.Anon: 3"
        end in
        check (op, args) sels false
      end
    | Bang (b, sels) ->
        self#expr scx (Bang (Apply (b, []) @@ b, sels) @@ e)
    | Apply ({core = Opaque name}, args) ->
      begin
        if List.mem name (fst scx) then begin
          Errors.err ~at:e
            "Warning: %s does not introduce any assumptions. \
             It does not make sense to use it here.\n" name;
          Internal (Builtin.TRUE) @@ e
        end else begin
          let args = List.map (self#expr scx) args in
          match Deque.find ~backwards:true (snd scx) (hyp_is_named name) with
            | Some (dep, {core = Defn ({core = Operator (_, op)} as opc,
                                       wd, _, _)}) ->
                standard_form ~cx:(snd scx) ~dep:(dep + 1) ~wd:wd
                  (op.core @@ e $$ opc) args
            | Some (dep, opc) ->
                if args = [] then
                  Ix (dep + 1) @@ e $$ opc
                else
                  Apply (Ix (dep + 1) @@ e, args) @@ e $$ opc
            | None ->
               Util.eprintf ~at:e "Operator \"%s\" not found" name ;
               Errors.set e (Printf.sprintf "Operator \"%s\" not found" name);
               failwith "Expr.Anon: 4"
        end
      end
    | Opaque _ -> self#expr scx (Apply (e, []) @@ e)
    | Parens (e, {core = Syntax}) -> self#expr scx e
    | _ -> super#expr scx e

  method hyp scx h = match h.core with
    | Fact (e, vis, NotSet) ->
      let adj (s, cx) h =
        (s, Deque.snoc cx h) in
        let e = self#expr scx e in
        let h = Fact (e, vis, E_temporal_props.compute_time (snd scx) e) @@ h in
        (adj scx h, h)
    | Fact (e, vis, ts) ->
      let adj (s, cx) h =
        (s, Deque.snoc cx h) in
        let e = self#expr scx e in
        let h = Fact (e, vis, ts) @@ h in
        (adj scx h, h)
    | _ -> super#hyp scx h

  method pform scx pf = match pf.core with
    | Nlabel (l, ns) ->
        let xs = List.map begin
          fun n -> match Deque.find ~backwards:true (snd scx) (hyp_is_named n.core) with
            | None ->
                Util.eprintf ~at:pf "Identifier \"%s\" in label parameters not found" n.core ;
                Errors.set pf (Printf.sprintf "Identifier \"%s\" in label parameters not found" n.core);
              failwith "Expr.Anon"
            | Some (dep, _) ->
                (n, dep + 1)
        end ns in
        Xlabel (l, xs) @@ pf
    | _ -> super#pform scx pf

  method defn scx df = match df.core with
    | Operator (nm, op) ->
        let op = match op.core with
          | Fcn _ ->
              let nscx = Visit.adj scx (Fresh (nm, Shape_expr, Constant, Unbounded) @@ nm) in
              let op = self#expr nscx op in
              let mk x = { op with core = x } in
              let occurs op =
                let op' = (app_expr (scons (Opaque "%%%" |> mk) (shift 1)) op) in
                not (Eq.expr op' op)
              in
                if occurs op then
                  Choose (nm, None,
                          Apply (Internal Builtin.Eq |> mk, [
                                   Ix 1 |> mk ;
                                   op
                                 ]) |> mk) |> mk
                else
                  app_expr (shift (-1)) op

          | _ ->
              self#expr scx op
        in
        Operator (nm, op) @@ df
    | _ ->
        super#defn scx df

end

class anon = object
  inherit anon_sg as super

  method expr scx e =
    Elab.desugar (super#expr scx e)
end

let anon = new anon

let _ = ()
