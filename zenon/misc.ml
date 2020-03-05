(*  Copyright 2003 INRIA  *)


(* functions missing from the standard library *)

let rec index n e = function
  | [] -> raise Not_found
  | h :: _ when h = e -> n
  | _ :: t -> index (n+1) e t
;;

let ( @@ ) = List.rev_append;;

exception False;;
exception True;;

let rec string_split s i =
  if String.length s <= i then []
  else if s.[i] = ' ' then string_split s (i + 1)
  else begin
    try
      let spc = String.index_from s i ' ' in
      String.sub s i (spc - i) :: string_split s (spc + 1)
    with Not_found -> [String.sub s i (String.length s - i)]
  end
;;

let string_split s = string_split s 0;;

let occurs sub str =
  let lsub = String.length sub in
  let lstr = String.length str in
  try
    for i = 0 to lstr - lsub do
      try
        for j = 0 to lsub - 1 do
          if str.[i+j] <> sub.[j] then raise False;
        done;
        raise True;
      with False -> ()
    done;
    false
  with True -> true
;;

let is_prefix sub str =
  String.length str >= String.length sub
  && String.sub str 0 (String.length sub) = sub
;;

let replace_first s1 s2 s =
  let l = String.length s in
  let l1 = String.length s1 in
  let rec loop i =
    if i + l1 > l then s
    else if String.sub s i l1 <> s1 then loop (i + 1)
    else begin
      String.sub s 0 i ^ s2 ^ String.sub s (i + l1) (l - i - l1)
    end
  in
  loop 0
;;

let rec xlist_init l f accu =
  if l = 0 then accu else xlist_init (l-1) f (f() :: accu)
;;

let list_init l f = xlist_init l f [];;

let isalnum c =
  match c with
  | 'A'..'Z' | 'a'..'z' | '0'..'9' -> true
  | _ -> false
;;

let isdigit c =
  match c with
  | '0'..'9' -> true
  | _ -> false
;;

let rec list_last l =
  match l with
  | [] -> raise Not_found
  | [x] -> x
  | h::t -> list_last t
;;

let rec xlist_iteri f l i =
  match l with
  | [] -> ()
  | h::t -> f i h; xlist_iteri f t (i+1);
;;

let list_iteri f l = xlist_iteri f l 0;;

let rec list_iter3 f l1 l2 l3 =
  match l1, l2, l3 with
  | h1 :: t1, h2 :: t2, h3 :: t3 -> f h1 h2 h3; list_iter3 f t1 t2 t3
  | [], [], [] -> ()
  | _, _, _ -> raise (Invalid_argument "list_iter3")
;;

let rec list_fold_left3 f a l1 l2 l3 =
  match l1, l2, l3 with
  | h1 :: t1, h2 :: t2, h3 :: t3 -> list_fold_left3 f (f a h1 h2 h3) t1 t2 t3
  | [], [], [] -> a
  | _ -> raise (Invalid_argument "list_fold_left3")
;;

let rec list_mapi f l i =
  match l with
  | [] -> []
  | h :: t -> f h i :: list_mapi f t (i+1)
;;

let rec list_map3 f l1 l2 l3 =
  match l1, l2, l3 with
  | h1 :: t1, h2 :: t2, h3 :: t3 -> f h1 h2 h3 :: list_map3 f t1 t2 t3
  | [], [], [] -> []
  | _ -> raise (Invalid_argument "list_map3")
;;

let rec list_map4 f l1 l2 l3 l4 =
  match l1, l2, l3, l4 with
  | h1 :: t1, h2 :: t2, h3 :: t3, h4 :: t4 ->
     f h1 h2 h3 h4 :: list_map4 f t1 t2 t3 t4
  | [], [], [], [] -> []
  | _ -> raise (Invalid_argument "list_map4")
;;

let rec list_unique_aux cmp l e accu =
  match l with
  | [] -> List.rev (e :: accu)
  | h :: t when cmp e h = 0 -> list_unique_aux cmp t e accu
  | h :: t -> list_unique_aux cmp t h (e :: accu)
;;

let list_sort_unique cmp l =
  match List.sort cmp l with
  | [] -> []
  | h :: t -> list_unique_aux cmp t h []
;;

let rec list_indexq_aux x l n =
  match l with
  | [] -> raise (Invalid_argument "list_indexq");
  | h :: t -> if h == x then n else list_indexq_aux x t (n + 1)
;;

let list_indexq x l = list_indexq_aux x l 0;;

let rec list_nth_tail l n =
  if n < 0 then raise (Invalid_argument "list_nth_tail");
  if n = 0 then l else
  match l with
  | [] -> raise (Invalid_argument "list_nth_tail")
  | h :: t -> list_nth_tail t (n - 1)
;;

let debug = Printf.eprintf;;

let base_n s x =
  if x = 0 then String.make 1 s.[0] else begin
    let b = String.length s in
    assert (x > 0);
    let rec conv x =
      if x = 0 then "" else Printf.sprintf "%s%c" (conv (x / b)) s.[x mod b]
    in
    conv x
  end
;;

let base26 x = base_n "abcdefghijklmnopqrstuvwxyz" x;;
