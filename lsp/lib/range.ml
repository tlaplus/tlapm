(* LSP ranges are 0-based and TLAPM is 1-based. In LSP the last char is exclusive. *)

module LspT = Lsp.Types

module Position : sig
  type t [@@deriving show]

  val make : int -> int -> t
  val of_pair : int * int -> t
  val as_pair : t -> int * int
  val as_string : t -> string
  val compare : t -> t -> int
  val less : t -> t -> bool
  val leq : t -> t -> bool
  val min : t -> t -> t
  val max : t -> t -> t
  val line : t -> int
end = struct
  type t = P of int * int [@@deriving show]

  let make l c = P (l, c)
  let of_pair (l, c) = P (l, c)
  let as_pair (P (l, c)) = (l, c)
  let as_string (P (l, c)) = Format.sprintf "%d:%d" l c

  (* Implement Map.OrderedType *)
  let compare (P (al, ac)) (P (bl, bc)) =
    let l = Stdlib.compare al bl in
    if l = 0 then Stdlib.compare ac bc else l

  let less (P (al, ac)) (P (bl, bc)) =
    match Stdlib.compare al bl with
    | 0 -> Stdlib.compare ac bc < 0
    | l_diff -> l_diff < 0

  let leq (P (al, ac)) (P (bl, bc)) =
    match Stdlib.compare al bl with
    | 0 -> Stdlib.compare ac bc <= 0
    | l_diff -> l_diff < 0

  let min a b = if less a b then a else b
  let max a b = if less a b then b else a
  let line (P (l, _)) = l
end

type t = R of (int * int) * (int * int) [@@deriving show]

let line_from (R ((fl, _), _)) = fl
let line_till (R (_, (tl, _))) = tl
let from (R ((fl, fc), _)) = Position.make fl fc
let till (R (_, (tl, tc))) = Position.make tl tc

(* Implement Map.OrderedType *)
let compare (R (af, at)) (R (bf, bt)) =
  let f = Position.compare (Position.of_pair af) (Position.of_pair bf) in
  if f = 0 then Position.compare (Position.of_pair at) (Position.of_pair bt)
  else f

let as_lsp_range (R ((fl, fc), (tl, tc))) =
  let open LspT in
  Range.create
    ~start:(Position.create ~line:(fl - 1) ~character:(fc - 1))
    ~end_:(Position.create ~line:(tl - 1) ~character:tc)

let of_lsp_range (range : LspT.Range.t) =
  let f = (range.start.line + 1, range.start.character + 1) in
  let t = (range.end_.line + 1, range.end_.character) in
  R (f, t)

let of_lsp_position (pos : LspT.Position.t) =
  R ((pos.line + 1, pos.character + 1), (pos.line + 1, pos.character))

let of_string_opt s =
  match String.split_on_char ':' s with
  | [ fl; fc; tl; tc ] ->
      let f = (int_of_string fl, int_of_string fc) in
      let t = (int_of_string tl, int_of_string tc - 1) in
      Some (R (f, t))
  | _ -> None

let of_locus (locus : Tlapm_lib.Loc.locus) =
  match (locus.start, locus.stop) with
  | Actual start_pt, Actual stop_pt ->
      Some (R ((start_pt.line, start_pt.col), (stop_pt.line, stop_pt.col - 1)))
  | Dummy, _ | _, Dummy -> None

let of_locus_opt (locus : Tlapm_lib.Loc.locus option) =
  match locus with None -> None | Some locus -> of_locus locus

let of_locus_must (locus : Tlapm_lib.Loc.locus) = Option.get (of_locus locus)
let of_wrapped prop = of_locus_opt (Tlapm_lib.Util.query_locus prop)
let of_wrapped_must prop = Option.get (of_wrapped prop)
let of_points f t = R (Position.as_pair f, Position.as_pair t)
let of_ints ~lf ~cf ~lt ~ct = R ((lf, cf), (lt, ct))
let of_lines fl tl = R ((fl, 1), (tl, 1))
let of_len (R ((fl, fc), _)) len = R ((fl, fc), (fl, fc + len - 1))
let make_before (R ((fl, fc), _)) = R ((fl, fc), (fl, fc - 1))
let make_before_ln (R ((fl, _), _)) = R ((fl, 1), (fl, 0))
let make_after (R (_, (tl, tc))) = R ((tl, tc + 1), (tl, tc + 1))

let join (R (af, at)) (R (bf, bt)) =
  let f = Position.min (Position.of_pair af) (Position.of_pair bf) in
  let t = Position.max (Position.of_pair at) (Position.of_pair bt) in
  of_points f t

let join_opt a b = match a with None -> b | Some a -> join a b
let crop_line_prefix (R ((lf, cf), t)) offset = R ((lf, cf + offset), t)

let string_of_range (R ((fl, fc), (tl, tc))) : string =
  Format.sprintf "%d:%d:%d:%d" fl fc tl tc

let string_of_pos p = Position.as_string p

(* Where to show the location of error for which the location is unknown. *)
let of_unknown = R ((1, 1), (1, 4))

(* To pass it to TLAPM for checking all the document. *)
let of_all = R ((0, 0), (0, 0))

(** [before p r] means range [r] is before point [p]. *)
let before p r = Position.less (till r) p

(** [touches a b] is true, if ranges [a] and [b] touches with their endpoints.
    Consider here that the ranges here are with the end character inclusive.
    I.e. "..-x:10" touches with "x:11-.." *)
let touches (R ((alf, acf), (alt, act))) (R ((blf, bcf), (blt, bct))) =
  (alt = blf && act + 1 = bcf) || (blt = alf && bct + 1 = acf)

(** [intersect a b] is true, if ranges [a] and [b] overlaps. *)
let intersect a b =
  Position.leq (from a) (till b) && Position.leq (from b) (till a)

(** [lines_intersect a b] is true if line ranges for [a] and [b] intersect. *)
let lines_intersect a b =
  let lfa = line_from a in
  let lta = line_till a in
  let lfb = line_from b in
  let ltb = line_till b in
  lfa <= ltb && lfb <= lta

(** [line_covered r p] is true, if the line of position [p] intersects with the
    range [r] lines. *)
let line_covered r p =
  let l = Position.line p in
  line_from r <= l && l <= line_till r

(* [lines_covered a b] is true if lines of [a] are fully covered by [b], i.e. [a] is inside of [b]. *)
let lines_covered a b =
  let lfa = line_from a in
  let lta = line_till a in
  let lfb = line_from b in
  let ltb = line_till b in
  lfb <= lfa && lta <= ltb

let lines_covered_or_all q rs =
  match List.filter (lines_intersect q) rs with
  | [] -> of_all
  | matching ->
      List.fold_left
        (fun acc m ->
          let from = Position.min (from acc) (from m) in
          let till = Position.max (till acc) (till m) in
          of_points from till)
        q matching

let first_diff_pos a b =
  let len = min (String.length a) (String.length b) in
  let rec count i l c =
    if i = len then Position.make l c
    else
      let ai = String.get a i in
      let bi = String.get b i in
      if ai = bi then
        let l, c =
          match bi with '\n' -> (l + 1, 1) | '\r' -> (l, c) | _ -> (l, c + 1)
        in
        count (i + 1) l c
      else Position.make l c
  in
  count 0 1 1

let%test_module "before" =
  (module struct
    let p35 = Position.make 3 5
    let%test _ = not (before p35 (R ((1, 1), (5, 3))))
    let%test _ = not (before p35 (R ((1, 1), (3, 6))))
    let%test _ = not (before p35 (R ((1, 1), (3, 5))))
    let%test _ = before p35 (R ((1, 1), (2, 5)))
  end)

let%test_module "first_diff_pos" =
  (module struct
    let test_fun a b = Position.as_pair (first_diff_pos a b)
    let%test "first" = (1, 1) = test_fun "hello" "bye"
    let%test "second" = (1, 2) = test_fun "hello" "hallo"
    let%test "next_ln" = (2, 1) = test_fun "sa\nme" "sa\ny"
    let%test "line_len_a" = (1, 3) = test_fun "same" "sa\n"
    let%test "line_len_b" = (1, 3) = test_fun "sa\n" "same"
    let%test "index_bounds_1" = (1, 3) = test_fun "mod" "mo"
    let%test "index_bounds_2" = (1, 3) = test_fun "mo" "mod"
  end)

let%test_module "lines_covered_or_all" =
  (module struct
    let some = R ((10, 5), (11, 20))
    let before1 = R ((1, 1), (2, 10))
    let on_from = R ((9, 1), (10, 6))
    let on_till = R ((10, 20), (15, 8))
    let within = R ((10, 20), (11, 10))
    let%test _ = of_all = lines_covered_or_all some [ before1 ]
    let%test _ = some = lines_covered_or_all some [ within ]

    let%test _ =
      R ((9, 1), (15, 8)) = lines_covered_or_all some [ on_from; on_till ]
  end)
