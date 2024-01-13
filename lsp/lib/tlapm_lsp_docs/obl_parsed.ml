type t = {
  obl : Tlapm_lib.Proof.T.obligation option;
  (* The following work as a cache. *)
  text_plain : string option Lazy.t;
  text_normalized : string option Lazy.t;
}

let obl_to_str obl =
  let buf = Buffer.create 100 in
  let fmt = Format.formatter_of_buffer buf in
  Tlapm_lib.Proof.Fmt.pp_print_obligation fmt obl;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let obl_to_normalized_str obl =
  obl_to_str (Tlapm_lib.Backend.Toolbox.normalize true obl)

let make obl =
  let text_plain = lazy (Option.map obl_to_str obl) in
  let text_normalized = lazy (Option.map obl_to_normalized_str obl) in
  { obl; text_plain; text_normalized }

let text_plain op = Lazy.force op.text_plain
let text_normalized op = Lazy.force op.text_normalized

let type_str op =
  match op.obl with
  | None -> "Ob_None"
  | Some o -> (
      match o.kind with
      | Ob_main -> "Ob_main"
      | Ob_support -> "Ob_support"
      | Ob_error e -> Format.sprintf "Ob_error %s" e)
