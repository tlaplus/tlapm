(*
 * Copyright (C) 2011  INRIA and Microsoft Corporation
 *)
open Printf
open Obj


(* NOTE:  This module uses Obj, but that's OK because this is
   DEBUGGING code.  Production code must NEVER use Obj. *)

let tag_name t =
  List.assoc t [
    lazy_tag, "lazy";
    closure_tag, "closure";
    object_tag, "object";
    infix_tag, "infix";
    forward_tag, "forward";
    abstract_tag, "abstract";
    string_tag, "string";
    double_tag, "double";
    double_array_tag, "double";
    custom_tag, "custom"]


let print i fmt =
    printf "%s%!" (String.make (2*i) ' ');
    printf fmt


let rec dump x i =
  let t = Obj.tag x in
  if t = int_tag then
    print i "%d\n" (Obj.obj x)
  else if t = out_of_heap_tag then
    print i "[[out-of-heap]]\n"
  else if t = unaligned_tag then
    print i "[[unaligned]]\n"
  else if t = string_tag then
    print i "%S\n" (Obj.obj x)
  else if t = double_tag || t = double_array_tag then begin
    let a = (Obj.obj x : float array) in
    print i "[| %g;" a.(0);
    for j = 1 to Array.length a - 1 do
      printf "\n";
      print i "   %g;" a.(j)
    done;
    printf " |]\n"
  end else if t >= no_scan_tag then
    print i "[[%s]]" (tag_name t)
  else begin
    let s = Obj.size x in
    print i "tag=%d size=%d\n" t s;
    for j = 0 to s - 1 do
            dump (Obj.field x j) (i + 1)
        done
  end
