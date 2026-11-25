module IntTable = Hashtbl.Make (Int)

type 'a entry = { value : 'a; from : int; till : int option }
type 'a t = { mutable out_counter : int; captured : 'a entry IntTable.t }

let create () : 'a t = { out_counter = 0; captured = IntTable.create 10 }

let setup (fmt : Format.formatter) (p : Format.stag -> (int * 'a) option) : 'a t
    =
  let cap = create () in
  Format.pp_set_mark_tags fmt true;
  let old_stag_functions = Format.pp_get_formatter_stag_functions fmt () in
  Format.pp_set_formatter_stag_functions fmt
    {
      old_stag_functions with
      mark_open_stag =
        (fun stag ->
          (match p stag with
          | Some (i, v) ->
              IntTable.add cap.captured i
                { value = v; from = cap.out_counter; till = None }
          | None -> ());
          "");
      mark_close_stag =
        (fun stag ->
          (match p stag with
          | Some (i, _v) ->
              let loc = IntTable.find cap.captured i in
              IntTable.replace cap.captured i
                { loc with till = Some cap.out_counter }
          | None -> ());
          "");
    };
  let old_out_functions = Format.pp_get_formatter_out_functions fmt () in
  Format.pp_set_formatter_out_functions fmt
    {
      old_out_functions with
      out_string =
        (fun str p n ->
          cap.out_counter <- cap.out_counter + n;
          old_out_functions.out_string str p n);
    };
  cap

let captured cap = IntTable.to_seq cap.captured |> Seq.map snd |> List.of_seq

let%test_module "" =
  (module struct
    (** An example, how to use this module. *)

    (** This part is printing-part dependent. We define a marker, a predicate
        recognizing it and mark the printed text as needed. The printing side
        don't need to know anything else. *)
    type Format.stag += Marker of int

    let is_stag_marker stag =
      match stag with Marker m -> Some (m, m) | _ -> None

    let pp_x fmt s =
      Format.pp_open_stag fmt (Marker 13);
      Fmt.string fmt s;
      Format.pp_close_stag fmt ()

    (* The function that wants to capture the positions will do the following:
       setup the formatter, do the printing and then get the captured ranges.
    *)
    let%test_unit "usage example" =
      let b = Buffer.create 10 in
      let fmt = Format.formatter_of_buffer b in
      (* ---- Setup the semantic tags. ---------------- *)
      let cap = setup fmt is_stag_marker in
      (* ---- Actual printing. ------------------------ *)
      Fmt.pf fmt "Some@[<v>@;%a@]" pp_x "thing";
      Format.pp_print_flush fmt ();
      (* ---- Assert the result. ---------------------- *)
      let captured = captured cap in
      assert (String.equal "Some\n    thing" (Buffer.contents b));
      assert ((List.hd captured).from = 9);
      assert ((List.hd captured).till = Some 14)
  end)
