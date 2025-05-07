open Tlapm_lib

class visitor_pp =
  object (self)
    val mutable acc : (Format.formatter -> unit) list = []

    method as_fmt (fmt : Format.formatter) : unit =
      let f' = acc in
      let () = acc <- [] in
      Format.pp_print_list
        ~pp_sep:(fun f _ -> Format.fprintf f ",@,")
        (fun f ff -> ff f)
        fmt (List.rev f')

    method add fmt = acc <- fmt :: acc

    method add_str str =
      acc <- (fun fmt -> Format.pp_print_string fmt str) :: acc

    method scope :
        'a.
        ((Format.formatter -> unit) -> Format.formatter -> unit) ->
        (unit -> 'a) ->
        'a =
      fun fmt f ->
        let rec split_at len l =
          match len with
          | 0 -> ([], l)
          | _ -> (
              match l with
              | [] -> ([], [])
              | x :: xs ->
                  let a, b = split_at (len - 1) xs in
                  (x :: a, b))
        in
        let len = List.length acc in
        let res = f () in
        let children, siblings = split_at (List.length acc - len) acc in
        let scope_fmt =
          fmt (fun fmt ->
              Format.pp_print_list
                ~pp_sep:(fun f _ -> Format.fprintf f ",@,")
                (fun f ff -> ff f)
                fmt (List.rev children))
        in
        acc <- scope_fmt :: siblings;
        res

    method scope_str : 'a. string -> (unit -> 'a) -> 'a =
      fun name f -> self#scope (Format.dprintf "%s{@[<hov>%t@]}" name) f
  end

  let rec _t_usable_fact (fmt : Format.formatter) (fact : Tlapm_lib__.Expr.T.expr) =
    let open Tlapm_lib in
    let nm =
      match fact.core with
      | Expr.T.Ix n -> "Ix" ^ string_of_int n
      | Expr.T.Opaque s -> "Opaque-" ^ s
      | Expr.T.Internal i -> (
          match i with
          | TRUE -> "TRUE"
          | FALSE -> "FALSE"
          | Implies -> "Implies"
          | Equiv -> "Equiv"
          | Conj -> "Conj"
          | Disj -> "Disj"
          | Neg -> "Neg"
          | Eq -> "Eq"
          | Neq -> "Neq"
          | STRING -> "STRING"
          | BOOLEAN -> "BOOLEAN"
          | SUBSET -> "SUBSET"
          | UNION -> "UNION"
          | DOMAIN -> "DOMAIN"
          | Subseteq -> "Subseteq"
          | Mem -> "Mem"
          | Notmem -> "Notmem"
          | Setminus -> "Setminus"
          | Cap -> "Cap"
          | Cup -> "Cup"
          | Prime -> "Prime"
          | StrongPrime -> "StrongPrime"
          | Leadsto -> "Leadsto"
          | ENABLED -> "ENABLED"
          | UNCHANGED -> "UNCHANGED"
          | Cdot -> "Cdot"
          | Actplus -> "Actplus"
          | Box true -> "Box(true)"
          | Box false -> "Box(false)"
          | Diamond -> "Diamond"
          | Nat -> "Nat"
          | Int -> "Int"
          | Real -> "Real"
          | Plus -> "Plus"
          | Minus -> "Minus"
          | Uminus -> "Uminus"
          | Times -> "Times"
          | Ratio -> "Ratio"
          | Quotient -> "Quotient"
          | Remainder -> "Remainder"
          | Exp -> "Exp"
          | Infinity -> "Infinity"
          | Lteq -> "Lteq"
          | Lt -> "Lt"
          | Gteq -> "Gteq"
          | Gt -> "Gt"
          | Divides -> "Divides"
          | Range -> "Range"
          | Seq -> "Seq"
          | Len -> "Len"
          | BSeq -> "BSeq"
          | Cat -> "Cat"
          | Append -> "Append"
          | Head -> "Head"
          | Tail -> "Tail"
          | SubSeq -> "SubSeq"
          | SelectSeq -> "SelectSeq"
          | OneArg -> "OneArg"
          | Extend -> "Extend"
          | Print -> "Print"
          | PrintT -> "PrintT"
          | Assert -> "Assert"
          | JavaTime -> "JaveTime"
          | TLCGet -> "TLCGet"
          | TLCSet -> "TLCSet"
          | Permutations -> "Permutations"
          | SortSeq -> "SortSeq"
          | RandomElement -> "RandomElement"
          | Any -> "Any"
          | ToString -> "ToString"
          | Unprimable -> "Unprimable"
          | Irregular -> "Irregular")
      | Expr.T.Lambda (_, _) -> "Lambda"
      | Expr.T.Sequent sq ->
          _t_sq fmt sq;
          "Sequent"
      | Expr.T.Bang (_, _) -> "Bang"
      | Expr.T.Apply (e, e_l) ->
          _t_usable_fact fmt e;
          List.iter (_t_usable_fact fmt) e_l;
          "Apply"
      | Expr.T.With (_, _) -> "With"
      | Expr.T.If (_, _, _) -> "If"
      | Expr.T.List (_, _) -> "List"
      | Expr.T.Let (_, _) -> "Let"
      | Expr.T.Quant (_, _, _) -> "Quant"
      | Expr.T.QuantTuply (_, _, _) -> "QuantTuply"
      | Expr.T.Tquant (_, _, _) -> "Tquant"
      | Expr.T.Choose (_, _, _) -> "Choose"
      | Expr.T.ChooseTuply (_, _, _) -> "ChooseTuply"
      | Expr.T.SetSt (_, _, _) -> "SetSt"
      | Expr.T.SetStTuply (_, _, _) -> "SetStTuply"
      | Expr.T.SetOf (_, _) -> "SetOf"
      | Expr.T.SetOfTuply (_, _) -> "SetOfTuply"
      | Expr.T.SetEnum _ -> "SetEnum"
      | Expr.T.Product _ -> "Product"
      | Expr.T.Tuple _ -> "Tuple"
      | Expr.T.Fcn (_, _) -> "Fcn"
      | Expr.T.FcnTuply (_, _) -> "FcnTuply"
      | Expr.T.FcnApp (_, _) -> "FcnApp"
      | Expr.T.Arrow (_, _) -> "Arrow"
      | Expr.T.Rect _ -> "Rect"
      | Expr.T.Record _ -> "Record"
      | Expr.T.Except (_, _) -> "Except"
      | Expr.T.Dot (_, _) -> "Dot"
      | Expr.T.Sub (_, _, _) -> "Sub"
      | Expr.T.Tsub (_, _, _) -> "Tsub"
      | Expr.T.Fair (_, _, _) -> "Fair"
      | Expr.T.Case (_, _) -> "Case"
      | Expr.T.String _ -> "String"
      | Expr.T.Num (_, _) -> "Num"
      | Expr.T.At _ -> "At"
      | Expr.T.Parens (_, _) -> "Parens"
    in
    match Property.query fact Proof.T.Props.use_location with
    | None ->
      Format.fprintf fmt " Fact %s" nm
    | Some loc -> Format.fprintf fmt "Loc %s" (Loc.string_of_locus loc)
  
  and _t_sq (fmt : Format.formatter) (sq : Tlapm_lib.Expr.T.sequent) =  (
    Format.fprintf fmt "=Ctx:";
    List.iter (t_hyp fmt) (Deque.to_list sq.context);
    Format.fprintf fmt "; Goal:";
  _t_usable_fact fmt sq.active;
  )
  and t_hyp (fmt : Format.formatter) (hy : Tlapm_lib.Expr.T.hyp) = (
    match hy.core with
    | Fresh (hint, _, _, hdom) -> (
      Eio.traceln "Fresh %s" hint.core;
      match hdom with
      | Unbounded -> Eio.traceln "Unbounded"
      | Bounded (expr, _) -> (
        Eio.traceln "Bounded";
        _t_usable_fact fmt expr;
      )
    )
    | FreshTuply (_, _) -> Eio.traceln "FreshTuply"
    | Flex (_) -> Eio.traceln "Flex"
    | Defn (defn, _, _, _) -> (
      match defn.core with
      | Recursive (hint, _) -> (
        Eio.traceln "Defn Recursive %s" hint.core
      )
      | Operator (hint, expr)  -> (
        Eio.traceln "Defn Operator %s" hint.core;
        _t_usable_fact fmt expr;
      )
      | Instance (hint, _)  -> (
        Eio.traceln "Defn Instance %s" hint.core
      )
      | Bpragma (hint, _, _) -> (
        Eio.traceln "Defn Bpragma %s" hint.core
      )
    )
    | Fact (fact, _, _) -> (
      _t_usable_fact fmt fact;
    )
  )
let rec pp_expr (fmt : Format.formatter) (expr : Expr.T.expr) : unit =
  let open Expr.T in
  match expr.core with
  | Ix i -> Format.fprintf fmt "Ix %d" i
  | Opaque n -> Format.fprintf fmt "Opaque %s" n
  | Internal b -> Format.fprintf fmt "Internal/%s" (Builtin.builtin_to_string b)
  | Lambda (_, _) -> Format.fprintf fmt "Lambda"
  | Sequent seq -> (
    Format.fprintf fmt "Sequent";
    _t_sq fmt seq;
    )
  | Bang (_, _) -> Format.fprintf fmt "Bang"
  | Apply (expr, args) ->
      Format.fprintf fmt "Apply{@[%a to %a@]}" pp_expr expr
        (Format.pp_print_list
           ~pp_sep:(fun f _ -> Format.fprintf f ",@,")
           pp_expr)
        args
  | With (_, _) -> Format.fprintf fmt "With"
  | If (_, _, _) -> Format.fprintf fmt "If"
  | List (_, exprr) -> (
    Format.fprintf fmt "List";
    Format.fprintf fmt "vals:%d" (List.length exprr);
    List.iter (fun expp -> (pp_expr fmt expp)) exprr
    )
  | Let (_, _) -> Format.fprintf fmt "Let"
  | Quant (_, _, exprr) -> (
    Format.fprintf fmt "Quant";
    pp_expr fmt exprr;
    )
  | QuantTuply (_, _, _) -> Format.fprintf fmt "QuantTuply"
  | Tquant (_, _, _) -> Format.fprintf fmt "Tquant"
  | Choose (_, _, _) -> Format.fprintf fmt "Choose"
  | ChooseTuply (_, _, _) -> Format.fprintf fmt "ChooseTuply"
  | SetSt (_, _, _) -> Format.fprintf fmt "SetSt"
  | SetStTuply (_, _, _) -> Format.fprintf fmt "SetStTuply"
  | SetOf (_, _) -> Format.fprintf fmt "SetOf"
  | SetOfTuply (_, _) -> Format.fprintf fmt "SetOfTuply"
  | SetEnum _ -> Format.fprintf fmt "SetEnum"
  | Product _ -> Format.fprintf fmt "Product"
  | Tuple _ -> Format.fprintf fmt "Tuple"
  | Fcn (_, _) -> Format.fprintf fmt "Fcn"
  | FcnTuply (_, _) -> Format.fprintf fmt "FcnTuply"
  | FcnApp (_, _) -> Format.fprintf fmt "FcnApp"
  | Arrow (_, _) -> Format.fprintf fmt "Arrow"
  | Rect _ -> Format.fprintf fmt "Rect"
  | Record _ -> Format.fprintf fmt "Record"
  | Except (_, _) -> Format.fprintf fmt "Except"
  | Dot (_, _) -> Format.fprintf fmt "Dot"
  | Sub (_, _, _) -> Format.fprintf fmt "Sub"
  | Tsub (_, _, _) -> Format.fprintf fmt "Tsub"
  | Fair (_, _, _) -> Format.fprintf fmt "Fair"
  | Case (_, _) -> Format.fprintf fmt "Case"
  | String _ -> Format.fprintf fmt "String"
  | Num (_, _) -> Format.fprintf fmt "Num"
  | At _ -> Format.fprintf fmt "At"
  | Parens (_, _) -> Format.fprintf fmt "Parens"

let pp_defn (fmt : Format.formatter) (defn : Expr.T.defn) : unit =
  let open Expr.T in
  match defn.core with
  | Recursive (_, _) -> Format.fprintf fmt "Recursive"
  | Operator (hint, expr) ->
      Format.fprintf fmt "Operator{hint=%s,expr=%a}" hint.core pp_expr expr
  | Instance (_, _) -> Format.fprintf fmt "Instance"
  | Bpragma (_, _, _) -> Format.fprintf fmt "Bpragma"

let pp_visibility (fmt : Format.formatter) (v : Expr.T.visibility) =
  let open Expr.T in
  match v with
  | Visible -> Format.fprintf fmt "Visible"
  | Hidden -> Format.fprintf fmt "Hidden"

let pp_export (fmt : Format.formatter) (v : Expr.T.export) =
  let open Expr.T in
  match v with
  | Local -> Format.fprintf fmt "Local"
  | Export -> Format.fprintf fmt "Export"

let pp_time (fmt : Format.formatter) (v : Expr.T.time) =
  let open Expr.T in
  match v with
  | Now -> Format.fprintf fmt "Now"
  | Always -> Format.fprintf fmt "Always"
  | NotSet -> Format.fprintf fmt "NotSet"

let pp_wheredef (fmt : Format.formatter) (v : Expr.T.wheredef) =
  let open Expr.T in
  match v with
  | Builtin -> Format.fprintf fmt "Builtin"
  | Proof time -> Format.fprintf fmt "Proof-%a" pp_time time
  | User -> Format.fprintf fmt "User"

let pp_hyp (fmt : Format.formatter) (hyp : Expr.T.hyp) : unit =
  let open Expr.T in
  match hyp.core with
  | Fresh (hint, _, _, _) -> Format.fprintf fmt "Fresh:%s" hint.core
  | FreshTuply (_, _) -> Format.fprintf fmt "FreshTuply"
  | Flex _ -> Format.fprintf fmt "Flex"
  | Defn (defn, wheredef, visibility, export) ->
      Format.fprintf fmt "Defn[%a:%a:%a]{%a}" pp_wheredef wheredef pp_visibility
        visibility pp_export export pp_defn defn
  | Fact (expr, _, _) -> Format.fprintf fmt "Fact{expr=%a}" pp_expr expr

let%test_unit "example use of visitor_pp" =
  let filename = "test_obl_expand.tla" in
  let content =
    String.concat "\n"
      [
        "---- MODULE test_obl_expand ----";
        "THEOREM TestA == FALSE";
        "    <1>1. TRUE OBVIOUS";
        "    <1>2. TRUE";
        "    <1>q. QED BY <1>1, <1>1, <1>2";
        "====";
      ]
  in
  let mule =
    Result.get_ok (Parser.module_of_string ~content ~filename ~loader_paths:[])
  in
  let vpp = new visitor_pp in
  let visitor =
    object (self : 'self)
      inherit Tlapm_lib.Module.Visit.map as m_super
      inherit [unit] Tlapm_lib.Proof.Visit.iter as p_super

      method! theorem cx name sq naxs pf orig_pf summ =
        vpp#scope
          (Format.dprintf "Theorem %a {@[<v>%t@]}"
             (Format.pp_print_option Tlapm_lib.Util.pp_print_hint)
             name)
        @@ fun () ->
        self#proof (Tlapm_lib.Expr.Visit.empty ()) pf;
        m_super#theorem cx name sq naxs pf orig_pf summ

      method! proof ctx pf : unit =
        vpp#scope (Format.dprintf "Proof{@[<v>%t@]}") @@ fun () ->
        p_super#proof ctx pf

      method! steps ctx sts =
        List.fold_left (fun ctx st -> self#step ctx st) ctx sts

      method! step ctx (st : Tlapm_lib.Proof.T.step) =
        vpp#scope (Format.dprintf "Step{@[<v>%t@]}") @@ fun () ->
        let open Tlapm_lib in
        vpp#add
          (Format.dprintf "[step=%a, %a]"
             (Format.pp_print_option Proof.T.pp_stepno)
             (Property.query st Proof.T.Props.step)
             Loc.pp_locus_compact_opt (Util.query_locus st));
        p_super#step ctx st

      method! expr ctx expr =
        vpp#scope (Format.dprintf "Expr{@[<hv>%a|%t@]}" pp_expr expr)
        @@ fun () -> p_super#expr ctx expr
    end
  in
  let _ = visitor#tla_module_root mule in
  (* Here we print all the collected output. *)
  Format.printf "Output {@[<v>%t@]}" vpp#as_fmt
