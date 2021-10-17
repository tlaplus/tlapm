(************************************************************************
*
*  typ_impgraph.ml      -- Implication graphs
*
*
*  Created by Hernán Vanzetto on 4 Nov 2013.
*  Copyright (c) 2013 __MyCompanyName__. All rights reserved.
*
************************************************************************)

open Ext
open Property

open Expr.T
open Expr.Subst
open Expr.Visit

open Printf
open List

module Smt = Smtcommons
module B = Builtin
(* module SMap = Map.Make (String) *)

open Typ_t
open Typ_e

(****************************************************************************)

let simp_list e =
  match e.core with
  | List (And,es) -> List (And, Smt.remove_repeated_ex es) %% []
  | List (Or,es) -> List (Or, Smt.remove_repeated_ex es) %% []
  | _ -> e

let mk_list = function
  | List (And,es) -> List (And, es) %% [] |> Smt.flatten_conj |> simp_list
  | List (Or,es) -> List (Or, es) %% [] |> Smt.flatten_disj |> simp_list
  | e -> e %% []

(****************************************************************************)

let in_fm = ref SMap.empty    (** node [i]  |->  list of formulas pointing to formula [i] *)
let in_ph = ref SMap.empty    (** node [i]  |->  list of formulas pointing to placeholder [i] *)
let out_fm = ref SMap.empty   (** node [i]  |->  list of formulas to which formula [i] points *)
let out_ph = ref SMap.empty   (** node [i]  |->  list of formulas to which placeholder [i] points *)
let plhdrs = ref SMap.empty

(****************************************************************************)

let ( @@ ) m k = try SMap.find k m with Not_found -> []

let madd m j ps =
  if ps = [] then () else m := SMap.add j (ps @ (!m @@ j)) !m

let mdel m j x =
  let xs = Smt.subtract (!m @@ j) x in
  m := if xs = [] then SMap.remove j !m else SMap.add j xs !m

let mremove m j =
  m := SMap.remove j !m

(* let rec first n = function
| [] -> []
| x :: xs -> if n < 1 then [] else x :: (first (n-1) xs) *)

(** Builds graph from VC implications *)
let mk_imp_graph vcs =
  let add1 (op,env,r1,r2) =
    (* assert (op = B.Implies) ; *)
    match op,r1,r2 with
    | B.Implies, Ph (_,p1), Ph (_,p2) when p1 <> p2 ->
        madd out_ph p1 [p2] ; madd in_ph p2 [p1]
    | B.Implies, Ph (_,p),  Ex (cx,e) -> madd out_fm p [Typ_e.to_cx env,e]
    | B.Implies, Ex (cx,e), Ph (_,p)  -> madd in_fm p [Typ_e.to_cx env,e]
    | _ -> ()
  in iter add1 vcs

(****************************************************************************)

(** Print formatted implication graph *)
let pp_imp b f_ph f_fm p = Util.eprintf "    @[%s = %s [%s] ; [%s]@]" p b
    (* (String.concat ", " (List.map (fun (Ph (_,p)) -> p) (!f_ph @@ p)))  *)
    (String.concat ", " (!f_ph @@ p))
    (String.concat ", " (List.map Smt.pps_ex (!f_fm @@ p)))

(****************************************************************************)

(** Pass the information upwards from fixed formulas.
    1. For each @k --> es
      make @k := And es.
    2. Cut the arrows. *)
let rule1 k =
  if !out_fm @@ k <> [] then begin
    let cx,ex =
      let cx = try let cx,_ = hd (!out_fm @@ k) in cx with _ -> [] in
      let es = List.map (fun (cx,e) -> e) (!out_fm @@ k) in                        (** FIX cx not used *)
      (* let es = rev es in *)
      let es =
        try let cx,ex = SMap.find k !plhdrs in ex :: es                       (** FIX cx not used *)
        with Not_found -> es
      in
      let ex = List (And, es) |> mk_list in
      cx,ex
    in
    plhdrs := SMap.add k (cx,ex) !plhdrs ;
    mremove out_fm k ;
  end else ()

(** Pass the information downwards from fixed formulas.
    For all [es] --> @k
      make @k := Or es.
    Cut the arrows. *)
let rule2 k =
  if !in_fm @@ k <> [] then begin
    let cx,ex =
      let cx = try let cx,_ = hd (!in_fm @@ k) in cx with _ -> [] in
      let es = List.map (fun (cx,e) -> e) (!in_fm @@ k) in                         (** FIX cx not used *)
      (* let es = rev es in *)
      (** new formula *)
      let es =
        try let cx,ex = SMap.find k !plhdrs in ex :: es                       (** FIX cx not used *)
        with Not_found -> es
      in
      let ex = List (Or, es) |> mk_list in
      cx,ex
    in
    plhdrs := SMap.add k (cx,ex) !plhdrs ;
    mremove in_fm k ;
  end else ()

let rule3 i =
  if !out_ph @@ i <> []
  && !out_fm @@ i = []
  && !in_fm @@ i = []
  (* && not (SMap.mem k !plhdrs)  *)
  then begin
    let ps = !out_ph @@ i in
    let ph k = try Some (SMap.find k !plhdrs) with _ -> None in
    let ff j =
      (*match ph i, ph j with
      | Some (cx,e1), Some (cx',e2) ->
          let ex = List (And, [e1 ; e2]) |> mk_list in
          plhdrs := SMap.add i (cx,ex) !plhdrs ;
          mdel out_ph i j ; mdel in_ph j i *)
      match ph i, ph j with
      | Some (cx,e1), Some (cx',e2) ->
          let ex = List (Or, [e1 ; e2]) |> mk_list in
          plhdrs := SMap.add j (cx,ex) !plhdrs ;
          mdel out_ph i j ; mdel in_ph j i
      | Some (cx,e1), None (* when !out_ph @@ j = [] *) ->
          plhdrs := SMap.add j (cx,e1) !plhdrs ;
          mdel out_ph i j ; mdel in_ph j i
      | None, Some (cx,e2) when !in_ph @@ i = [] ->
          plhdrs := SMap.add i (cx,e2) !plhdrs ;
          mdel out_ph i j ; mdel in_ph j i
      | _ -> ()
    in
    iter ff ps ;
  end else ()

let rec fix ns c rule x =
  let eq p q = SMap.equal (fun (cx,e) (cx',e') -> Expr.Eq.expr e e') p q in
  if c = 0 then (failwith "typesystem/typ_impgraph.ml: Cannot reach fixed point (for eq_phs).\n") else
  let x = !plhdrs in
  iter rule ns ;
  let x' = !plhdrs in
  (* Util.eprintf "---------------------------------------" ; SMap.iter Typ_c.pp_ph x' ; *)
  if eq x x' then () else fix ns (c-1) rule x

let solve_ph ns =
  fix ns 10 rule1 !plhdrs ;
  fix ns 10 rule2 !plhdrs ;
  fix ns 30 rule3 !plhdrs

(** Finally, undefined placeholders are assigned TRUE *)
let rule_true i =
  if !in_ph @@ i <> [] then begin
    let ps = !in_ph @@ i in
    let e = [], Internal B.TRUE %% [] in
    iter (fun j -> plhdrs := SMap.add j e !plhdrs) (i :: ps)
  end else ()
;;

(** [init_phs] : initial plhdrs
    [vcs] : verification conditions in the form (env,tref1,tref2)
    [ns] : total number of plhdrs
    Returns: plhdrs derived from the implication graph generated from [vcs]
    *)
let solve init_phs vcs ns =
  in_fm := SMap.empty ;
  in_ph := SMap.empty ;
  out_fm := SMap.empty ;
  out_ph := SMap.empty ;
  plhdrs := init_phs ;
  mk_imp_graph vcs ;

  (* if (ns <> []) then begin
  Smt.ifprint 3 "-- Initial graph --------------------------------------------" ;
  Smt.ifprint 3 "  in:" ; iter (pp_imp "\\/" in_ph in_fm) ns ;
  Smt.ifprint 3 "  out:" ; iter (pp_imp "/\\" out_ph out_fm) ns ;
  end; *)

  solve_ph ns ;
  (* solve_ph ns ; *)
  (* solve_ph ns ; *)

  iter rule_true ns ;                                                         (** Undefined placeholders are assigned TRUE *)

  (* if (ns <> []) then begin
  Smt.ifprint 3 "-- Final graph ----------------------------------------------" ;
  Smt.ifprint 3 "  in:" ;  iter (pp_imp "\\/" in_ph in_fm) ns ;
  Smt.ifprint 3 "  out:" ; iter (pp_imp "/\\" out_ph out_fm) ns ;
  end; *)

  Smt.ifprint 3 "-- Placeholders ---------------------------------------------" ;
  SMap.iter Typ_c.pp_ph !plhdrs ;

  !plhdrs
