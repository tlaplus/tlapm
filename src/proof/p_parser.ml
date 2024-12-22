(*
 * proof/parser.ml --- proof parser
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext
open Property
open Expr.T

open P_t

let qed_loc_prop : Loc.locus pfuncs = make ~uuid:"2fb9a59e-6c30-11ee-b962-0242ac120002" "Parser.qed_loc"

let enlarge_loc x y =
  Util.locate x (Loc.merge (Util.get_locus x) (Util.get_locus y))

type preno =
  | Star of string
  | Plus of string
  | Num of int * string

let set_level n = function
  | Star l | Plus l | Num (_, l) ->
      match l with
        | "" -> Unnamed (n, Std.unique ())
        | _ -> Named (n, l, false)

type supp = Emit | Suppress
type only = Default | Only

let annotate supp meth x =
  let x = match supp with
    | Suppress -> assign x Props.supp ()
    | _ -> x
  in
  let x = match meth with
    | Some meth -> assign x Props.meth [meth]
    | _ -> x
  in x

type preproof_ =
  | PreBy       of supp * only * usable * Method.t option
  | PreObvious  of supp * Method.t option
  | PreOmitted  of omission
  | PreStep     of bool * preno * prestep

and prestep =
  | PreHide     of usable
  | PreUse      of supp * only * usable * Method.t option
  | PreDefine   of defn list
  | PreAssert   of sequent
  | PreSuffices of sequent
  | PreCase     of expr
  | PrePick     of bound list * expr
  | PrePickTuply of tuply_bounds * expr
  | PreHave     of supp * expr * Method.t option
  | PreTake     of supp * bound list * Method.t option
  | PreTakeTuply of supp * tuply_bounds * Method.t option
  | PreWitness  of supp * expr list * Method.t option
  | PreQed

type step_or_qed =
  | STEP of step
  | QED of Loc.locus * proof

exception Backtrack

let rec to_proof currlv = function
  | [] ->
      (Omitted Implicit @@ currlv, [])
  | {core = PreBy (supp, onl, us, meth)} as p :: ps ->
      let p = By (us, onl = Only) @@ p in
      let p = Property.assign p Props.step (Unnamed (currlv.core, 0)) in
      (annotate supp meth p, ps)
  | {core = PreObvious (supp, meth)} as p :: ps ->
      let p = Obvious @@ p in
      (annotate supp meth p, ps)
  | {core = PreOmitted om} as p :: ps ->
      (Omitted om @@ p, ps)
  | ps -> begin
      try
        let (ss, qp, ps) = to_steps ~first:true currlv ps in
        let sloc = List.fold_left begin
          fun l s -> Loc.merge l (Util.get_locus s)
        end (try Util.get_locus qp.core with _ -> Util.get_locus (get_qed_proof qp.core)) ss in
        let prf = Util.locate (Steps (ss, qp.core)) sloc in
        let prf = Property.assign prf Props.step (Property.get qp Props.step) in
        (prf, ps)
      with Backtrack ->
        (Omitted Implicit @@ currlv, ps)
    end

and to_steps ?(first = false) currlv ps = match ps with
  | {core = PreStep (kwd, sn, st)} as p :: ps ->
      if not first && kwd then begin
        Errors.set p "PROOF keyword found in step that does not begin subproof" ;
        Util.eprintf ~at:p "PROOF keyword found in step that does not begin subproof\n%!" ;
        failwith "Proof.Parser"
      end ;
      let thislv = match sn, kwd, first with
        | Num (n, _), _, _ -> n
        | Star _, true, true ->
            (*
             * Util.eprintf ~at:p
             *   "%d: <*> -> %d (because first and PROOF)\n%!"
             *   currlv.core currlv.core ;
             *)
            currlv.core
        | Star _, false, true ->
            (*
             * Util.eprintf ~at:p
             *   "%d: <*> -> %d (because first and no PROOF)\n%!"
             *   currlv.core (currlv.core - 1) ;
             *)
            currlv.core - 1
        | Star _, _, false ->
            assert (not kwd) ;
            (*
             * Util.eprintf ~at:p
             *   "%d: <*> -> %d (because not first)\n%!"
             *   currlv.core currlv.core ;
             *)
            currlv.core
        | Plus _, _, false ->
            Errors.set p "<+> used but no subproof expected" ;
              Util.eprintf ~at:p "<+> used but no subproof expected\n%!" ;
            failwith "Proof.Parser"
        | Plus _, _, _ ->
            (*
             * Util.eprintf ~at:p
             *   "%d: <+> -> %d\n%!"
             *   currlv.core currlv.core ;
             *)
            currlv.core
      in
      if thislv < currlv.core then raise Backtrack ;
      if not first && thislv > currlv.core then raise Backtrack ;
      let sn = set_level thislv sn in begin
        match to_step thislv (st @@ p) ps with
          | (STEP s, nps) ->
              let s = Property.assign s Props.step sn in
              let thislv = Util.locate thislv (Loc.right_of (Util.get_locus s)) in
              let (ss, qp, ps) = to_steps thislv nps in
              (s :: ss, qp, ps)
          | (QED (qed_loc, qp), ps) ->
              let loc = Loc.merge qed_loc (Util.get_locus qp) in
              let qp = Util.locate (Qed qp) loc in
              let qp = Property.assign qp Props.step sn in
              let qp = Property.assign qp qed_loc_prop qed_loc in
              let qp = Util.locate qp loc in
              let qp = Property.assign qp Props.step sn in
              let qp = Property.assign qp qed_loc_prop qed_loc in
              ([], qp, ps)
      end
  | p :: _ ->
      let found = match p.core with
           | PreObvious _ -> "n OBVIOUS"
           | PreOmitted _ -> "n OMITTED"
           | PreBy _ -> " BY"
           | _ -> Errors.bug ~at:p "to_steps: is a step after all?"
      in
      Errors.set p (Printf.sprintf "Expecting a proof step but found a%s leaf proof\n" found);
      Util.eprintf ~at:p
           "Expecting a proof step but found a%s leaf proof\n" found;
      failwith "Proof.Parser"
  | [] ->
      Util.eprintf ~at:currlv
        "Unexpected end of (sub)proof at level %d before QED step\n%!" currlv.core ;
      Errors.set currlv ("Unexpected end of (sub)proof at level "^(string_of_int currlv.core)^" before QED step\n");
      failwith "Proof.Parser"

and to_step currlv st ps =
  match st.core with
  | PreQed ->
      let qed_loc = Util.get_locus st in
      let (p, ps) = to_proof (currlv + 1 @@ st) ps in
      (QED (qed_loc, p), ps)
  | PreHide us ->
      (STEP (Hide us @@ st), ps)
  | PreUse (supp, onl, us, meth) ->
      let u = Use (us, onl = Only) @@ st in
      (STEP (annotate supp meth u), ps)
  | PreDefine dfs ->
      (STEP (Define dfs @@ st), ps)
  | PreHave (supp, e, meth) ->
      let h = Have e @@ st in
      (STEP (annotate supp meth h), ps)
  | PreTake (supp, bs, meth) ->
      let t = Take bs @@ st in
      (STEP (annotate supp meth t), ps)
  | PreTakeTuply (supp, bs, meth) ->
      let t = TakeTuply bs @@ st in
      (STEP (annotate supp meth t), ps)
  | PreWitness (supp, es, meth) ->
      let w = Witness es @@ st in
      (STEP (annotate supp meth w), ps)
  | PreAssert sq ->
      let (p, ps) = to_proof (currlv + 1 @@ st) ps in
      let st = enlarge_loc st p in
      (STEP (Assert (sq, p) @@ st), ps)
  | PreSuffices sq ->
      let (p, ps) = to_proof (currlv + 1 @@ st) ps in
      let st = enlarge_loc st p in
      (STEP (Suffices (sq, p) @@ st), ps)
  | PreCase e ->
      let (p, ps) = to_proof (currlv + 1 @@ st) ps in
      let st = enlarge_loc st p in
      (STEP (Pcase (e, p) @@ st), ps)
  | PrePick (bs, e) ->
      let (p, ps) = to_proof (currlv + 1 @@ st) ps in
      let st = enlarge_loc st p in
      (STEP (Pick (bs, e, p) @@ st), ps)
  | PrePickTuply (bs, e) ->
      let (p, ps) = to_proof (currlv + 1 @@ st) ps in
      let st = enlarge_loc st p in
      (STEP (PickTuply (bs, e, p) @@ st), ps)

let toplevel ps =
  let ps = match ps with
    | [] -> failwith "toplevel"
    | p :: ps ->
        let pc = match p.core with
          | PreStep (_, pn, pstp) ->
              PreStep (true, pn, pstp)
          | _ -> p.core
        in { p with core = pc } :: ps
  in
  match to_proof (0 @@ (List.hd ps)) ps with
    | (p, []) -> p
    | (_, p :: _) ->
        Errors.set p "extra step(s) after finished proof" ;
        Util.eprintf ~at:p "extra step(s) after finished proof" ;
        failwith "Proof.Parser.toplevel"


let make_pick_from_boundeds
        (boundeds: Expr.Parser.boundeds)
        (predicate: expr):
            prestep =
    if Expr.Parser.has_tuply_bounded boundeds
    then
        let bs = Expr.Parser.tuply_bounds_of_boundeds
            boundeds in
        PrePickTuply (bs, predicate)
    else
        let bs = Expr.Parser.bounds_of_boundeds
            boundeds in
        PrePick (bs, predicate)


let make_take_from_boundeds
        (boundeds: Expr.Parser.boundeds)
        supp
        meth:
            prestep =
    if Expr.Parser.has_tuply_bounded boundeds
    then
        let bs = Expr.Parser.tuply_bounds_of_boundeds
            boundeds in
        PreTakeTuply (supp, bs, meth)
    else
        let bs = Expr.Parser.bounds_of_boundeds
            boundeds in
        PreTake (supp, bs, meth)


module Parser = struct
  open Expr.Parser
  open Tla_parser.P
  open Tla_parser

  let read_method = optional (use Method_prs.read_method)

  let suppress = lazy begin
    choice [
      pragma (punct "_" <|> ident "suppress") <!> Suppress ;
      succeed Emit ;
    ]
  end

  let preno =
    scan begin
      function
        | Token.ST (sn, sl, nd) -> Some begin
            match sn with
              | `Star -> Star sl
              | `Plus -> Plus sl
              | `Num n -> Num (n, sl)
          end
        | _ ->
            None
    end

  let only =
    choice [ kwd "ONLY" <!> Only ;
             succeed Default ]

  let proof_kwd =
    choice [ kwd "PROOF" <!> true ;
             succeed false ]

  let sequent = lazy begin
    choice [
      use (Expr.Parser.sequent false);
      use (expr false) <$> (fun e -> { context = Deque.empty ; active = e })
    ]
  end

  let rec preproof = lazy begin
    proof_kwd >>= fun pk ->
      choice [
        use suppress >>= begin fun supp ->
          choice [
            locate (kwd "BY") <**> only <**> use usebody <*> read_method
            <$> (fun (((by, onl), us), meth) -> PreBy (supp, onl, us, meth) @@ by) ;

            locate begin
              kwd "OBVIOUS" >>> read_method
              <$> (fun meth -> PreObvious (supp, meth))
            end ;
          ]
        end ;

        locate (kwd "OMITTED" <!> (PreOmitted Explicit)) ;

        locate begin
          preno <**> use prestep
          <$> (fun (pn, stp) -> PreStep (pk, pn, stp))
        end ;
      ]
  end

  and prestep = lazy begin
    choice [
      kwd "QED" <!> PreQed ;

      kwd "HIDE" >*> use usebody <$> (fun us -> PreHide us) ;

      kwd "SUFFICES" >*> use sequent <$> (fun sq -> PreSuffices sq) ;

      kwd "CASE" >*> use (expr false) <$> (fun e -> PreCase e) ;

      kwd "PICK" >*>
      (quantifier_boundeds false) <**>
      (colon_expr false)
      <$> (fun (boundeds, predicate) ->
          make_pick_from_boundeds
              boundeds predicate);

      use suppress >>= begin fun supp ->
        choice [
          kwd "USE" >*> only <*> use usebody <*> read_method
          <$> (fun ((onl, us), meth) -> PreUse (supp, onl, us, meth)) ;

          kwd "HAVE" >*> use (expr false) <*> read_method
          <$> (fun (e, meth) -> PreHave (supp, e, meth)) ;

          kwd "TAKE" >*>
              (quantifier_boundeds false) <*>
              read_method
              <$> (fun (boundeds, meth) ->
                  make_take_from_boundeds
                      boundeds supp meth);

          kwd "WITNESS" >*> sep1 (punct ",") (use (expr false)) <*> read_method
          <$> (fun (es, meth) -> PreWitness (supp, es, meth)) ;
        ]
      end ;

      attempt (optional (kwd "DEFINE") >>> star1 (use (defn false)))
      <$> (fun dfs -> PreDefine dfs) ;

      use sequent <$> (fun sq -> PreAssert sq) ;
    ]
  end

  (* In a usebody, a step name has special meaning, so we strip the
     Bang and let it be the underlying Opaque identifier, which will
     be bound to the assumptions of the corresponding step.  Only
     step names can be represented by a Bang with an empty list of
     selectors.
     See the "operator" case at the end of function expr_or_op
     in file e_parser.ml.
  *)
  and filter_usebody_fact f =
    match f.core with
    | Bang ({core = Opaque v} as e, []) when v.[0] = '<' -> e
    | _ -> f

  and usebody = lazy begin
    let defs =
      (kwd "DEF" <|> kwd "DEFS") >*> sep1 (punct ",") (use definable)
    in
    sep (punct ",") (use (expr false)) >>= function
      | [] ->
          defs <$> (fun ds -> { facts = [] ; defs = ds })
      | fs ->
          optional defs <$> begin function
            | None -> { facts = List.map filter_usebody_fact fs ; defs = [] }
            | Some ds -> { facts = List.map filter_usebody_fact fs ; defs = ds }
          end
  end

  and definable = lazy begin
    locate begin
      sep1 (punct "!") (choice [ anyop ; anyident ])
      <$> (fun ids -> Dvar (String.concat "!" ids))
    end
  end

  let rec preproofs = lazy begin
    choice [
      use preproof <**> use preproofs
      <$> (fun (p, ps) -> p :: ps) ;

      succeed [] ;
    ]
  end

  let proof = lazy begin
    choice [
      use preproof <**> use preproofs
      <$> (fun (p, ps) -> p :: ps) ;

      locate (succeed (PreOmitted Implicit))
      <$> (fun pp -> [pp])
    ] <$> toplevel
  end

end

let usebody = Parser.usebody
let proof = Parser.proof
let suppress = Parser.suppress
