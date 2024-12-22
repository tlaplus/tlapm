(*
 * proof/fmt.ml --- proofs (pretty printing)
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

(* START dflags
 *
 *      "proof"   goals when printing proofs (i.e., --debug rep)
 *
 * END dflags *)

open Ext

open Property

open Expr.T
open Expr.Fmt

open Format
open Fmtutil

open P_t

let step_name x = match Property.query x Props.step with
  | None -> "<?>?"
  | Some sn -> string_of_stepno sn

let step_dot x = match Property.query x Props.step with
  | Some (Unnamed _) -> ""
  | _ -> "."

let rec extend_with (hx, vx) hs = match Deque.front hs with
  | None -> (hx, vx)
  | Some (h, hs) ->
      let cx = match h.core with
        | Flex nm
        | Fresh (nm, _, _, _)
        | Defn ({core = Operator (nm, _)}, _, _, _) ->
            (hx, Ctx.push vx nm.core)
        | Fact (_, _, _) ->
            (hx, Ctx.bump vx)
        | _ -> failwith "Proof_fmt.extend_with"
      in
        extend_with cx hs


let pp_print_obligation ff ob =
  ignore (pp_print_sequent (Deque.empty, Ctx.dot) ff ob.obl.core)

let prmeth what ff =
  let f m =
    Format.pp_print_string ff " " ;
    Method.pp_print_method ff m;
  in
  Option.iter (List.iter f) (query what Props.meth)


let is_omitted prf = match prf.core with
  | Omitted _ -> true
  | _ -> false

let rec pp_print_proof cx ff prf =
  match query prf Props.orig_proof with
    | Some orig_prf when not (Params.debugging "noby") ->
        let orig_prf = match prf.core with
          | Steps (first :: _, qed) ->
              if has first Props.goal then
                assign orig_prf Props.goal (get first Props.goal)
              else orig_prf
          | Steps ([], qed) ->
              if has qed Props.goal then
                assign orig_prf Props.goal (get qed Props.goal)
              else orig_prf
          | _ ->
              orig_prf
        in
        pp_print_proof cx ff orig_prf
    | _ ->
        fprintf ff "@[<v0>" ;
        if not (is_omitted prf) && (Params.debugging "proof" || Params.debugging "leafproofs") then begin
          let not_steps = match prf.core with
            | Steps _ -> false
            | _ -> true
          in
          if not_steps && has prf Props.goal then begin
            fprintf ff
              "@[<hv3>(* goal =@ @[%a@] *)@]@,(* %s *)@,"
              (Expr.Fmt.pp_print_expr (Deque.empty, Ctx.dot)) (Sequent (get prf Props.goal) @@ prf)
              (Util.location prf) ;
          end ;
          if has prf Props.obs then begin
            fprintf ff
              "@[<h>(* #obligations = %d *)@]@,"
              (List.length (get prf Props.obs))
          end
        end ;
        let supp = if has prf Props.supp then"(*{_}*)" else "" in
        begin match prf.core with
        | By (us, onl) ->
            fprintf ff "%sBY %s@[<b0>%a%t@]"
              supp
              (if onl then "ONLY " else "")
              (pp_print_usable cx) us
              (prmeth prf)
        | Obvious ->
            fprintf ff "%sOBVIOUS%t" supp (prmeth prf)
        | Omitted h ->
            fprintf ff "%sOMITTED%s" supp begin
              match h with
                | Explicit -> ""
                | Implicit -> " (* implicit *)"
                | Elsewhere loc -> Printf.sprintf " (* see %s *)" (Loc.string_of_locus ~cap:false loc)
            end
        | Steps (inits, qed) ->
            let cx =
              pp_print_delimited_fold
                ~sep:(fun ff () -> ())
                (fun cx ff stp ->
                   fprintf ff "@[<hv2>%s%s "
                     (step_name stp) (step_dot stp) ;
                   let cx = pp_print_step cx ff stp in
                   fprintf ff "@]@," ;
                   cx)
                cx ff inits
            in
            fprintf ff "@[<hv2>%s%s QED%a@]"
              (step_name prf) (step_dot prf)
              (pp_print_qed_step(*proof_nl*) cx) qed
        | Error msg ->
            fprintf ff "%sERROR (*%s*)" supp msg
        end;
        fprintf ff "@]"

and pp_print_step cx ff stp =
  if Params.debugging "proof" then begin
    if has stp Props.goal then begin
      if not (has stp Props.orig_step) then pp_force_newline ff () ;
      fprintf ff
        "@[<hv3>(* goal =@ @[%a@] *)@]@\n(* %s *)@\n"
        (Expr.Fmt.pp_print_expr (Deque.empty, Ctx.dot)) (Sequent (get stp Props.goal) @@ stp)
        (Util.location stp) ;
    end ;
    (* if has stp Props.obs then begin *)
    (*   fprintf ff *)
    (*     "@[<h>(\* #obligations = %d *\)@]@\n" *)
    (*     (List.length (get stp Props.obs)) *)
    (* end *)
  end ;
  begin match query stp Props.orig_step with
    | None -> ()
    | Some stp -> begin
        (* pp_force_newline ff () ; *)
        match stp.core with
          | Have e ->
              fprintf ff "(* @[<h>HAVE %a@] *)@\n" (pp_print_expr cx) e
          | Take bs ->
              let (_, nbs) = extend_bounds cx bs in
              fprintf ff "(* @[<h>TAKE @[<b0>%a@]@] *)@\n"
                (pp_print_delimited (pp_print_bound cx)) nbs
          | Witness es ->
              fprintf ff "(* @[<h>WITNESS @[<b0>%a@]@] *)@\n"
                (pp_print_delimited (pp_print_expr cx)) es
          | Pcase (e, _) ->
              fprintf ff "(* @[<h>CASE %a@] *)@\n" (pp_print_expr cx) e
          | Pick (bs, e, _) ->
              let (ecx, nbs) = extend_bounds cx bs in
              fprintf ff "(* @[<b2>PICK %a :@ %a@] *)@\n"
                (pp_print_delimited (pp_print_bound cx)) nbs
                (pp_print_expr ecx) e
          | _ -> ()
      end
  end ;
  let stepnm = step_name stp @@ stp in
  let cx = match stp.core with
    | Forget k ->
        fprintf ff "FORGET EXCEPT %d" k ;
        cx
    | Hide us ->
        fprintf ff "HIDE @[<b0>%a@]" (pp_print_usable cx) us ;
        cx
    | Use (us, onl) ->
        if has stp Props.supp then fprintf ff "(*{_}*)" ;
        fprintf ff "@[<b2>USE %s@[<b0>%a@]%t@]"
          (if onl then "ONLY " else "")
          (pp_print_usable cx) us
          (prmeth stp) ;
        List.fold_left (fun cx _ -> bump cx) cx us.facts
    | Define dfs ->
        pp_open_vbox ff 0 ;
        let cx = pp_print_defns cx ff dfs in
        pp_close_box ff () ;
        cx
    | Assert (sq, p) ->
        ignore (pp_print_sequent cx ff sq) ;
        begin
          (* assumptions *)
          let pcx = extend_with cx sq.context in
          (* negation of old goal *)
          let pcx = bump pcx in
          (* step name *)
          let (pcx, _) = adj pcx stepnm in
          (* hidden fact that it is true *)
          let pcx = bump pcx in
          pp_print_proof_nl pcx ff p ;
        end ;
        let (cx, _) = adj cx stepnm in
        bump cx
    | Pcase (e, p) ->
        fprintf ff "@[<b2>CASE@ %a@]" (pp_print_expr cx) e ;
        begin
          (* negation of old goal + new assumption *)
          let pcx = bump (bump cx) in
          (* step name definition and fact *)
          let (pcx, _) = adj pcx stepnm in
          (* hidden fact that it is true *)
          let pcx = bump pcx in
          pp_print_proof_nl pcx ff p ;
        end ;
        let (cx, _) = adj cx stepnm in
        bump cx
    | Suffices (sq, p) ->
        fprintf ff "@[<b2>SUFFICES@ %t@]"
          (fun ff -> ignore (pp_print_sequent cx ff sq)) ;
        begin match Deque.null sq.context, p.core with
          | false, _
          | _, Steps _ -> pp_force_newline ff ()
          | _ -> pp_print_space ff ()
        end ;
        begin
          (* step name definition and fact *)
          let (cx, _) = adj cx stepnm in
          let cx = bump cx in
          pp_print_proof cx ff p ;
        end ;
        (* new context *)
        let cx = extend_with cx sq.context in
        (* negation of old goal *)
        let cx = bump cx in
        (* step name definition *)
        let (cx, _) = adj cx stepnm in
        (* hidden fact that it is true *)
        bump cx
    | Have e ->
        if has stp Props.supp then fprintf ff "(*{_}*) " ;
        fprintf ff "@[<b2>HAVE@ %a%t@]" (pp_print_expr cx) e (prmeth stp) ;
        (* negation of old goal + hidden fact *)
        let cx = bump (bump cx) in
        (* step name definition *)
        let (cx, _) = adj cx stepnm in
        (* hidden fact that it is true *)
        bump cx
    | Take bs ->
        if has stp Props.supp then fprintf ff "(*{_}*)" ;
        (* assumptions *)
        let (cx, bsf) = fmt_bounds cx bs in
        fprintf ff "@[<b2>TAKE@ %t%t@]" bsf (prmeth stp) ;
        (* negation of old goal *)
        let cx = bump cx in
        (* step name definition *)
        let (cx, _) = adj cx stepnm in
        (* hidden fact that it is true *)
        bump cx
    | Witness es ->
        if has stp Props.supp then fprintf ff "(*{_}*)" ;
        fprintf ff "@[<b2>WITNESS@ @[<b0>%a%t@]@]"
          (pp_print_delimited (pp_print_expr cx)) es (prmeth stp) ;
        (* no new assumptions *)
        (* negation of old goal *)
        let cx = bump cx in
        (* step name definition *)
        let (cx, _) = adj cx stepnm in
        (* hidden fact that it is true *)
        bump cx
    | Pick (bs, e, p) ->
        let (ecx, bsf) = fmt_bounds cx bs in
        fprintf ff "@[<b2>PICK %t :@ %a@]%a"
          bsf
          (pp_print_expr ecx) e
          (pp_print_proof_nl (bump (bump (bump cx)))) p ;
        (* step name + fact for existential *)
        let cx = bump (bump cx) in
        (* identifiers for PICK *)
        let (cx, _) = extend_bounds cx bs in
        (* body of PICK *)
        let cx = bump cx in
        (* negation of old goal *)
        let cx = bump cx in
        (* step name definition for the SUFFICES *)
        let cx = bump cx in
        (* conjunction of nondom facts in the SUFFICES *)
        bump cx
    | TakeTuply _
    | PickTuply _ ->
        assert false
  in cx

and pp_print_qed_step cx ff q =
  match q.core with Qed p -> pp_print_proof cx ff p

and pp_print_usable cx ff us = match us.facts, List.map defop us.defs with
  | [], [] -> assert false
  | [], defs ->
      fprintf ff "DEF%s @[%a@]"
        (if List.length defs = 1 then "" else "S")
        (pp_print_delimited (pp_print_expr cx)) defs
  | facts, [] ->
      fprintf ff "%a" (pp_print_delimited (pp_print_expr cx)) facts
  | facts, defs ->
      fprintf ff "@[%a@]@ DEF%s @[%a@]"
        (pp_print_delimited (pp_print_expr cx)) facts
        (if List.length defs = 1 then "" else "S")
        (pp_print_delimited (pp_print_expr cx)) defs

and defop dw = match dw.core with
  | Dvar id -> { dw with core = Opaque id }
  | Dx n -> { dw with core = Ix n }

and pp_print_proof_nl cx ff prf =
  let () = match prf.core with
    | Steps _ -> pp_force_newline ff () ;
    | _ -> pp_print_space ff ()
  in pp_print_proof cx ff prf

let string_of_step cx e =
    let b = Buffer.create 10 in
    let fmt = Format.formatter_of_buffer b in
    ignore (pp_print_step (cx, Ctx.dot) fmt e);
    Format.pp_print_flush fmt () ;
    Buffer.contents b
