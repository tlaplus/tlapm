type t = {
  text : string; (* Contents if the file at the specific version. *)
  version : int;
}

let make txt vsn = { text = txt; version = vsn }
let text tv = tv.text
let version tv = tv.version
let diff_pos a b = Range.first_diff_pos a.text b.text
