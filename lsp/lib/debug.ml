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
  | List (_, _) -> Format.fprintf fmt "List"
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
