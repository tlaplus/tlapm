(*
 * ext.ml --- extensions to standard libraries
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

module Option = struct
  let iter : ('a -> unit) -> 'a option -> unit =
    fun fn -> function
      | Some x -> fn x
      | None -> ()
  let map : ('a -> 'b) -> 'a option -> 'b option =
    fun fn -> function
      | Some x -> Some (fn x)
      | None -> None
  let default : 'a -> 'a option -> 'a =
    fun x -> function
      | Some y -> y
      | None -> x
  let is_none : 'a option -> bool =
    function
      | None -> true
      | _ -> false
  let is_some : 'a option -> bool =
    function
      | Some _ -> true
      | _ -> false
  exception No_value
  let get : 'a option -> 'a =
    function
      | Some x -> x
      | _ -> raise No_value
end

module List = struct
  include List

  (*
   * The functions in this module are tail recursive.  This is
   * needed because the lists that occur at runtime can get very large.
   *)

  let map fn xs = rev (rev_map fn xs);;

  let rec rev_mapi fn xs i accu =
    match xs with
    | [] -> accu
    | x :: xs -> rev_mapi fn xs (i+1) (fn i x :: accu)
  ;;
  let mapi fn xs = rev (rev_mapi fn xs 0 []);;

  let rec rev_filter_map fn xs accu =
    match xs with
    | [] -> accu
    | x :: xs ->
       match fn x with
       | None -> rev_filter_map fn xs accu
       | Some y -> rev_filter_map fn xs (y :: accu)
  ;;
  let filter_map fn xs = rev (rev_filter_map fn xs []);;

  let iteri : (int -> 'a -> unit) -> 'a list -> unit =
    fun fn xs ->
      let rec loop n = function
        | [] -> ()
        | x :: xs ->
            fn n x ;
            loop (n + 1) xs
      in
      loop 0 xs

  let find_exc : ('a -> bool) -> exn -> 'a list -> 'a =
    fun sel ex xs ->
      let rec scan = function
        | [] -> raise ex
        | x :: xs ->
            if sel x then x
            else scan xs
      in
      scan xs

  let rec rev_init k n f accu =
    if k >= n then accu else rev_init (k+1) n f (f k :: accu)
  ;;
  let init n f = rev (rev_init 0 n f []);;

  let rec rev_unique cmp xs accu =
    match xs with
    | [] -> accu
    | x :: xs ->
       if exists (cmp x) accu
       then rev_unique cmp xs accu
       else rev_unique cmp xs (x :: accu)
  ;;
  let unique ?(cmp = (=)) xs = rev (rev_unique cmp xs []);;

  let sort ?(cmp = Pervasives.compare) = List.sort cmp

  exception Invalid_index

  let split_nth n xs =
    let rec loop n xs accu =
      match n, xs with
      | 0, _ -> (rev accu, xs)
      | _, [] -> raise Invalid_index
      | _, x :: xs -> loop (n - 1) xs (x :: accu)
    in
    loop n xs []
  ;;

end

module Std = struct

  let unique : unit -> int =
    let count = ref 0 in
    fun () ->
      incr count ;
      !count

  let finally : (unit -> unit) -> ('a -> 'b) -> 'a -> 'b =
    fun cleanup fn x ->
      try
        let y = fn x in
        cleanup () ;
        y
      with ex ->
        cleanup () ;
        raise ex

  let input_all : ?bsize:int -> in_channel -> string =
    fun ?(bsize = 19) ch ->
      let buf = Buffer.create bsize in
      let str = Bytes.create 64 in
      let rec loop () =
        let hmany = Pervasives.input ch str 0 64 in
        if hmany > 0 then begin
          Buffer.add_subbytes buf str 0 hmany ;
          loop ()
        end
      in
      loop () ;
      Buffer.contents buf

  let input_file : ?bin:bool -> string -> string =
    fun ?(bin = false) fname ->
      let fsize = (Unix.stat fname).Unix.st_size in
      let ch =
        if bin then Pervasives.open_in_bin fname
        else Pervasives.open_in fname in
      finally
        (fun () -> Pervasives.close_in ch)
        (input_all ~bsize:fsize) ch

  let input_list ch =
    let accu = ref [] in
    try while true do
      accu := Pervasives.input_line ch :: !accu;
    done; assert false
    with End_of_file -> List.rev !accu
  ;;

  let identity : 'a -> 'a =
    fun x -> x

end

  let string_contains s1 s2 =
    let re = Str.regexp_string s2 in
    try ignore (Str.search_forward re s1 0); true
    with Not_found -> false

let is_prefix pref txt =
  String.length txt >= String.length pref
  && String.sub txt 0 (String.length pref) = pref
;;

let split s c =
  let len = String.length s in
  let rec spin base cur accu =
    if cur >= len then
      List.rev (String.sub s base (cur - base) :: accu)
    else if s.[cur] = c then
      spin (cur+1) (cur+1) (String.sub s base (cur - base) :: accu)
    else
      spin base (cur+1) accu
  in
  spin 0 0 []
;;
