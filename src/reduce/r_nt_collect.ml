(*
 * reduce/nt_collect.ml --- collect data for notypes encoding
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Expr.T
open Type.T
open Util.Coll
open Property

open R_nt_axioms
open R_nt_table

module B = Builtin
module C = R_nt_cook
module D = Type.Disambiguation

let rec atoms_in_aux acc (TKind (ks, t)) =
  let s = get_atom t in
  let acc =
    if List.exists (fun s' -> s = s') acc then acc
    else s :: acc
  in
  List.fold_left atoms_in_aux acc ks

let atoms_in k = atoms_in_aux [] k

let atoms_to_nodes ss =
  List.map begin function
    | TU -> [ NT_U ]
    | TStr -> [ NT_Str ]
    | _ -> []
  end ss |> List.concat

let visitor = object (self : 'self)
  inherit [unit, nt_node Sm.t] Expr.Visit.fold as super

  method expr scx ns oe =
    match oe.core with
    | Internal B.STRING ->
        add NT_String ns
    | Internal B.BOOLEAN ->
        add NT_Boolean ns
    | Internal B.SUBSET ->
        add NT_Power ns
    | Internal B.UNION ->
        add NT_Union ns
    | Internal B.Subseteq ->
        add NT_Subseteq ns
    | Internal (B.Mem | B.Notmem) ->
        add NT_Mem ns
    | Internal B.Setminus ->
        add NT_Setminus ns
    | Internal B.Cap ->
        add NT_Cap ns
    | Internal B.Cup ->
        add NT_Cup ns

    | Opaque s when s = D.u_any ->
        add NT_UAny ns
    | Opaque s when s = D.s_any ->
        add NT_StringAny ns
    | Opaque s when s = D.cast_nm TBool TU ->
        add NT_BoolToU ns
    | Opaque s when s = D.cast_nm TStr TU ->
        add NT_StringToU ns
    | Opaque s when has oe C.setst_prop ->
        (* FIXME set s *)
        let k = get oe C.setst_prop in
        add (NT_SetSt (s, k)) ns

    | Lambda (vs, e) ->
        let ns = List.fold_left begin fun ns (v, _) ->
          let k = get_kind v in
          let ns' = atoms_to_nodes (atoms_in k) in
          List.fold_right add ns' ns
        end ns vs in
        super#expr scx ns oe

    | Tquant (_, hs, _) ->
        let ns = List.fold_left begin fun ns h ->
          match get_sort h with
          | TU -> add NT_U ns
          | TStr -> add NT_Str ns
          | _ -> ns
        end ns hs in
        super#expr scx ns oe

    | Choose (h, _, _)
    | SetSt (h, _, _) ->
        let ns =
          match get_sort h with
          | TU -> add NT_U ns
          | TStr -> add NT_Str ns
          | _ -> ns
        in
        super#expr scx ns oe

    | SetEnum es ->
        let n = List.length es in
        let ns = add (NT_Enum n) ns in
        super#expr scx ns oe

    | _ -> super#expr scx ns oe

  method bounds scx ns bs =
    let scx, ns = super#bounds scx ns bs in
    let ns = List.fold_left begin fun ns (v, _, _) ->
      match get_sort v with
      | TU -> add NT_U ns
      | TStr -> add NT_Str ns
      | _ -> ns
    end ns bs in
    scx, ns

  method defn scx ns df =
    match df.core with
    | Recursive (h, _)
    | Operator (h, _) ->
        let k = get_kind h in
        let ns' = atoms_to_nodes (atoms_in k) in
        let ns = List.fold_right add ns' ns in
        super#defn scx ns df

    | _ -> super#defn scx ns df

  method hyp scx ns hyp =
    match hyp.core with
    | Fresh (h, _, _, _)
    | Flex h ->
        let k = get_kind h in
        let ns' = atoms_to_nodes (atoms_in k) in
        let ns = List.fold_right add ns' ns in
        super#hyp scx ns hyp

    | _ -> super#hyp scx ns hyp

end

let collect sq =
  snd (visitor#sequent ((), Deque.empty) Sm.empty sq)
