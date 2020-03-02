(*
 * reduce/nt_table.ml --- notypes encoding table
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Expr.T
open Type.T
open Deps
open Util.Coll
open Property

open R_nt_axioms


(* {3 General} *)

type hyp_nm = R_nt_cook.hyp_nm

type nt_node =
  (* Set Theory *)
  | NT_U
  | NT_UAny
  | NT_Mem
  | NT_Subseteq
  | NT_Enum of int
  | NT_Union
  | NT_Power
  | NT_Cup
  | NT_Cap
  | NT_Setminus
  | NT_SetSt of hyp_nm option * string * ty_kind * expr
  (*| NT_SetOf of string * ty_kind*)  (* TODO *)
  (* Booleans *)
  | NT_BoolToU
  | NT_Boolean
  (* Strings *)
  | NT_Str
  | NT_StringAny
  | NT_StringToU
  | NT_String
  | NT_StringLit of string
  (* TODO functions, arith, tuples, sequences, etc. *)

let nt_get_id node =
  match node with
  | NT_U -> "nt_u"
  | NT_Str -> "nt_str"
  | NT_UAny -> "nt_uany"
  | NT_StringAny -> "nt_stringany"
  | NT_Mem -> "nt_mem"
  | NT_Subseteq -> "nt_subseteq"
  | NT_Enum n -> "nt_enum_" ^ string_of_int n
  | NT_Union -> "nt_union"
  | NT_Power -> "nt_power"
  | NT_Cup -> "nt_cup"
  | NT_Cap -> "nt_cap"
  | NT_Setminus -> "nt_setminus"
  | NT_SetSt (_, s, _, _) -> "nt_setst_" ^ s
  | NT_Boolean -> "nt_boolean"
  | NT_BoolToU -> "nt_booltou"
  | NT_String -> "nt_string"
  | NT_StringToU -> "nt_stringtou"
  | NT_StringLit s -> "nt_stringlit_" ^ s

(* FIXME compile with >= 4.06.0 *)
let update id upd_f ns =
  if Sm.mem id ns then
    let n = Sm.find id ns in
    match upd_f (Some n) with
    | None -> Sm.remove id ns
    | Some n' -> Sm.add id n' ns
  else
    match upd_f None with
    | None -> Sm.remove id ns
    | Some n -> Sm.add id n ns

let add_update n = function
  | None -> Some n
  | Some n' when n = n' -> Some n'
  | Some n' -> invalid_arg ("Reduce.NtTable.add_update: \
                            duplicate node '" ^ (nt_get_id n) ^ "'")

let add n ns = update (nt_get_id n) (add_update n) ns

let union ns1 ns2 =
  Sm.merge begin fun id n1 n2 ->
    match n1, n2 with
    | None, None -> None
    | Some n, None | None, Some n -> Some n
    | Some n1, Some n2 ->
        if n1 = n2 then Some n1
        else invalid_arg ("Reduce.NtTable.union: \
                          duplicate nodes '" ^ id ^ "'")
  end ns1 ns2

let from_list ns =
  List.fold_right add ns Sm.empty

(* NOTE dirty addition *)
(* When I first implemented this module, I thought new declarations could all
 * go in a top context (if we just put them in the right order).
 * Then I realized that for specialized second-order operators, this is not so
 * simple.  For e.g. if something like { x \in S : P(x, y, ..) } occurs, this is
 * replaced by a first-order application like F(S, y, ..), with F being
 * axiomatized.  But *that* axioms cannot be inserted above the declarations of
 * global variables in P(x, y, ..), so it cannot go to the top...
 * As a corrective, I added this function that assigns an optional string to
 * every node.  If this string is present, it signals that the new declarations
 * associated with the node should go just below the hypothesis with that name.
 *)
let nt_get_place = function
  | NT_SetSt (nm, _, _, _) -> nm
  | _ -> None


(* {3 NT Specification} *)

let nt_base = from_list [ NT_U ; NT_UAny ; NT_Mem ]

let nt_get_deps_l node =
  match node with
  | NT_U -> []
  | NT_UAny -> [ NT_U ]
  | NT_Mem -> [ NT_U ]
  | NT_Subseteq -> [ NT_U ; NT_Mem ]
  | NT_Enum _ -> [ NT_U ; NT_Mem ]
  | NT_Union -> [ NT_U ; NT_Mem ]
  | NT_Power -> [ NT_U ; NT_Mem ]
  | NT_Cup -> [ NT_U ; NT_Mem ]
  | NT_Cap -> [ NT_U ; NT_Mem ]
  | NT_Setminus -> [ NT_U ; NT_Mem ]
  | NT_SetSt _ -> [ NT_U ; NT_Mem ]

  | NT_BoolToU -> [ NT_U ; NT_Mem ]
  | NT_Boolean -> [ NT_U ; NT_Mem ; NT_BoolToU ]

  | NT_Str -> []
  | NT_StringAny -> [ NT_Str ]
  | NT_StringToU -> [ NT_U ; NT_Mem ]
  | NT_String -> [ NT_U ; NT_Mem ; NT_StringToU ]
  | NT_StringLit _ -> [ NT_U ; NT_Mem ; NT_StringToU ; NT_String ]

let nt_get_deps node =
  List.fold_left begin fun sm node ->
    Sm.add (nt_get_id node) node sm
  end Sm.empty (nt_get_deps_l node)

let stringlits = ref Ss.empty

let nt_get_hyps node =
  let hs =
    match node with
    | NT_U | NT_Str -> []

    | NT_UAny -> [ uany_decl ]
    | NT_Mem -> [ mem_decl ]
    | NT_Subseteq -> [ subseteq_decl ; subseteq_fact ]
    | NT_Enum n -> [ enum_decl n ; enum_fact n ]
    | NT_Union -> [ union_decl ; union_fact ]
    | NT_Power -> [ power_decl ; power_fact ]
    | NT_Cup -> [ cup_decl ; cup_fact ]
    | NT_Cap -> [ cap_decl ; cap_fact ]
    | NT_Setminus -> [ setminus_decl ; setminus_fact ]
    | NT_SetSt (_, s, k, e) -> [ setst_decl s k ; setst_fact s k e ]

    | NT_BoolToU -> [ booltou_decl ]
    | NT_Boolean -> [ boolean_decl ; boolean_fact ]

    | NT_StringAny -> [ stringany_decl ]
    | NT_StringToU -> [ stringtou_decl ; stringcast_fact ]
    | NT_String -> [ string_decl ; string_fact ]

    | NT_StringLit s ->
        if Ss.mem s !stringlits then []
        else
          let previous_lits = Ss.elements !stringlits in
          let distinct_facts = List.map begin fun s' ->
            stringlit_distinct_fact s s'
          end previous_lits in
          stringlits := Ss.add s !stringlits;
          stringlit_decl s :: distinct_facts
  in
  Deque.of_list hs


(* {3 Make Utilities} *)

module NT_Graph : Graph
  with type node = nt_node
   and type s = (int * hyp Deque.dq) Deque.dq * expr (* yikes *) =
struct
  type node = nt_node
  (* Shattered sequent.  The context is divided into parcels, which are joined
   * at the end of the axiomatization process.  A parcel is split when some
   * hypothesis has to be inserted in the middle.  The first parcel is treated
   * as a special top context, where hypotheses go by default.  For each parcel
   * we also record the number of hypotheses that were appended at the rear;
   * this is used to compute a substitution to apply to some axioms. *)
  type s = (int * hyp Deque.dq) Deque.dq * expr

  let base = nt_base
  let get_id n = nt_get_id n
  let get_deps n = nt_get_deps n

  let app_hss_e sub (hss, e) =
    let (sub, hss) =
      Deque.fold_left begin fun (sub, hss') (k, hs) ->
        let sub, hs = Expr.Subst.app_hyps sub hs in
        (sub, Deque.snoc hss' (k, hs))
      end (sub, Deque.empty) hss
    in
    let e = Expr.Subst.app_expr sub e in
    (hss, e)

  let do_split k dq =
    let rec spin k l r =
      if k = 0 then (l, r)
      else
        let x, r = Deque.front r |> Option.get in
        spin (k - 1) (Deque.snoc l x) r
    in
    spin k Deque.empty dq

  let split_hss nm hss =
    let test = (fun h -> hyp_name h = nm) in
    let rec spin l r =
      match Deque.front r with
      | None -> invalid_arg ("Reduce.NtTable.split_hss: \
                              cannot find hypothesis '" ^ nm ^ "'")
      | Some ((k, hs), r) ->
          begin match Deque.find hs test with
          | None ->
              spin (Deque.snoc l (k, hs)) r
          | Some (p, _) ->
              let hs_left, hs_right = do_split (p + 1) hs in
              (* Relevant hyp at the rear of l.  So l is non-empty *)
              (* The number of added hyps in the left split parcel is 0
               * as we assume all splits occur between original hypotheses. *)
              let l = Deque.snoc l (0, hs_left) in
              let r = (* FIXME can hs_right really be empty? *)
                if Deque.size hs_right = 0 then r
                else Deque.cons (k, hs_right) r
              in
              (l, r)
          end
    in
    spin Deque.empty hss

  let get_ac n (hss, e) =
    match nt_get_place n with
    | None ->
        let (k, top), hss = Option.get (Deque.front hss) in
        let more = nt_get_hyps n in
        let p = Deque.size more in
        let top = Deque.append top more in
        let sub = Expr.Subst.shift p in
        let (hss, e) = app_hss_e sub (hss, e) in
        (Deque.cons (k + p, top) hss, e)
    | Some nm ->
        let (hss_left, hss_right) = split_hss nm hss in
        let more = nt_get_hyps n in
        let _, sub = Deque.fold_right begin fun (k, hs) (d, sub) ->
          let sub' = Expr.Subst.bumpn d (Expr.Subst.shift k) in
          let sub = Expr.Subst.compose sub' sub in
          let n = Deque.size hs in
          (d + n, sub)
        end hss_left (0, Expr.Subst.shift 0) in
        let _, more = Expr.Subst.app_hyps sub more in
        let hss_left, (k, hs) = Option.get (Deque.rear hss_left) in
        let hs = Deque.append hs more in
        let p = Deque.size more in
        let sub = Expr.Subst.shift p in
        let (hss_right, e) = app_hss_e sub (hss_right, e) in
        (Deque.append (Deque.snoc hss_left (k + p, hs)) hss_right, e)
end

module NT_Axiomatize = Closure (NT_Graph)

let nt_axiomatize ns sq =
  let x = ([ 0, Deque.empty ; 0, sq.context ] |> Deque.of_list, sq.active) in
  let x = NT_Axiomatize.ac_deps ns x in
  Deque.fold_right begin fun (_, hs) sq ->
    { sq with context = Deque.append hs sq.context }
  end (fst x) { context = Deque.empty ; active = snd x }
