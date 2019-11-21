(*
 * Copyright (C) 2012  INRIA and Microsoft Corporation
 *)

(*
Revision.f "$Rev$";;
*)

let rev = ref "";;
let f x = if x > !rev then rev := x;;

f "$Rev$";;

let get () = String.sub !rev 6 (String.length !rev - 8);;
