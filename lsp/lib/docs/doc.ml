open Util

(* Max number of unprocessed/pending versions to keep. *)
let keep_vsn_count = 50

type t = {
  uri : LspT.DocumentUri.t;
  pending : Doc_vsn.t list;
      (** All the received but not yet processed versions. *)
  actual : Doc_actual.t;  (** Already processed version. *)
}

let make uri tv = { uri; pending = []; actual = Doc_actual.make uri tv None }

let add doc tv =
  let drop_till = Doc_vsn.version tv - keep_vsn_count in
  let drop_unused = List.filter (fun pv -> Doc_vsn.version pv < drop_till) in
  { doc with pending = tv :: drop_unused doc.pending }

let latest_vsn doc =
  match doc.pending with
  | [] -> Doc_actual.vsn doc.actual
  | latest :: _ -> Doc_vsn.version latest

let set_actual_vsn doc vsn =
  if Doc_actual.vsn doc.actual = vsn then Some doc
  else
    let rec drop_after_vsn = function
      | [] -> (None, [])
      | (pv : Doc_vsn.t) :: pvs ->
          if Doc_vsn.version pv = vsn then (Some pv, [])
          else
            let res, pvs = drop_after_vsn pvs in
            (res, pv :: pvs)
    in
    let selected, pending = drop_after_vsn doc.pending in
    match selected with
    | None -> None
    | Some selected ->
        let actual = Doc_actual.make doc.uri selected (Some doc.actual) in
        Some { doc with actual; pending }

let with_actual doc f =
  let doc, act, res = f doc doc.actual in
  let doc = { doc with actual = act } in
  (doc, res)
