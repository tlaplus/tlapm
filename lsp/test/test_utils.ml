module MultilineDiff : sig
  (** For comparing module texts showing multiline diff. *)

  include Alcotest.TESTABLE

  val same : t
  val diff : string -> string -> t
end = struct
  module Diff = Simple_diff.Make (String)

  type t = Same | Differs of Diff.t

  let same = Same

  let diff a b =
    let line_array s = String.split_on_char '\n' s |> Array.of_list in
    let diff = Diff.get_diff (line_array a) (line_array b) in
    let same =
      List.for_all
        (fun d ->
          match d with
          | Diff.Deleted _ | Diff.Added _ -> false
          | Diff.Equal _ -> true)
        diff
    in
    if same then Same else Differs diff

  let string_of_diff (diff : Diff.t) : string =
    diff
    |> List.map (fun d ->
           match d with
           | Diff.Deleted lines ->
               lines |> Array.to_list |> List.map (fun l -> "- " ^ l)
           | Diff.Added lines ->
               lines |> Array.to_list |> List.map (fun l -> "+ " ^ l)
           | Diff.Equal lines ->
               lines |> Array.to_list |> List.map (fun l -> "  " ^ l))
    |> List.flatten |> String.concat "\n"

  let pp fmt (t : t) =
    match t with
    | Same -> Fmt.string fmt "Same"
    | Differs d -> Fmt.pf fmt "Differs\n%s" (string_of_diff d)

  let equal a b =
    match (a, b) with
    | Same, Same -> true
    | Same, Differs _ -> false
    | Differs _, Same -> false
    | Differs _, Differs _ -> failwith "cannot compare non empty diffs"
end

let check_multiline_diff ~title ~expected ~actual =
  Alcotest.check
    (module MultilineDiff)
    title MultilineDiff.same
    (MultilineDiff.diff expected actual)

let check_multiline_diff_td ~title ~expected ~actual =
  check_multiline_diff ~title ~expected ~actual:(Lsp.Text_document.text actual)
