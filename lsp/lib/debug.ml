let unwrap = Tlapm_lib.Property.unwrap

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
      fun name f -> self#scope (Format.dprintf "%s{%t}" name) f
  end

let pp_visibility fmt (v : Tlapm_lib.Expr.T.visibility) =
  match v with
  | Tlapm_lib.Expr.T.Visible -> Fmt.pf fmt "Visible"
  | Tlapm_lib.Expr.T.Hidden -> Fmt.pf fmt "Hidden"

let pp_bullet fmt (v : Tlapm_lib.Expr.T.bullet) =
  match v with
  | Tlapm_lib.Expr.T.And -> Fmt.pf fmt "And"
  | Tlapm_lib.Expr.T.Or -> Fmt.pf fmt "Or"
  | Tlapm_lib.Expr.T.Refs -> Fmt.pf fmt "Refs"

let pp_expr_text cx fmt expr =
  Fmt.pf fmt "@[%a@]"
    (Tlapm_lib.Expr.Fmt.pp_print_expr (cx, Tlapm_lib.Ctx.dot))
    expr

let pp_expr (fmt : Format.formatter) (expr : Tlapm_lib.Expr.T.expr) : unit =
  let open Tlapm_lib.Expr.T in
  match expr.core with
  | Ix i -> Format.fprintf fmt "Ix %d" i
  | Opaque n -> Format.fprintf fmt "Opaque %s" n
  | Internal b ->
      Format.fprintf fmt "Internal/%s" (Tlapm_lib.Builtin.builtin_to_string b)
  | Lambda (_, _) -> Format.fprintf fmt "Lambda"
  | Sequent _ -> Format.fprintf fmt "Sequent"
  | Bang (_, _) -> Format.fprintf fmt "Bang"
  | Apply (_, _) -> Format.fprintf fmt "Apply"
  | With (_, _) -> Format.fprintf fmt "With"
  | If (_, _, _) -> Format.fprintf fmt "If"
  | List (b, exs) ->
      Format.fprintf fmt "List/%d-%a" (List.length exs) pp_bullet b
  | Let (_, _) -> Format.fprintf fmt "Let"
  | Quant (_, _, _) -> Format.fprintf fmt "Quant"
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

let pp_defn (fmt : Format.formatter) (defn : Tlapm_lib.Expr.T.defn) : unit =
  match defn.core with
  | Tlapm_lib.Expr.T.Recursive (n, _) ->
      Format.fprintf fmt "Recursive %s" (unwrap n)
  | Tlapm_lib.Expr.T.Operator (n, _) ->
      Format.fprintf fmt "Operator %s" (unwrap n)
  | Tlapm_lib.Expr.T.Instance (n, _) ->
      Format.fprintf fmt "Instance %s" (unwrap n)
  | Tlapm_lib.Expr.T.Bpragma (n, _, _) ->
      Format.fprintf fmt "Bpragma %s" (unwrap n)

let pp_hyp (fmt : Format.formatter) (hyp : Tlapm_lib.Expr.T.hyp) : unit =
  match hyp.core with
  | Tlapm_lib.Expr.T.Fresh (hint, _, _, _) ->
      Format.fprintf fmt "Fresh %s" (unwrap hint)
  | Tlapm_lib.Expr.T.FreshTuply (_, _) -> Format.fprintf fmt "FreshTuply"
  | Tlapm_lib.Expr.T.Flex hint -> Format.fprintf fmt "Flex %s" (unwrap hint)
  | Tlapm_lib.Expr.T.Defn (defn, _, _, _) ->
      Format.fprintf fmt "Defn %a" pp_defn defn
  | Tlapm_lib.Expr.T.Fact (expr, visible, _) ->
      Format.fprintf fmt "@[Fact/%a %a@]" pp_visibility visible pp_expr expr

let pp_cx (fmt : Format.formatter)
    (cx : Tlapm_lib.Expr.T.hyp Tlapm_lib.Util.Deque.dq) : unit =
  Fmt.pf fmt "@[%a@]"
    (Fmt.list ~sep:Format.pp_force_newline pp_hyp)
    (Tlapm_lib.Util.Deque.to_list cx)

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
