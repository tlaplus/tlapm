(*  Copyright 2009 INRIA  *)

type lexeme =
  | String of string
  | Int of string
;;

let rec count_digits s n i =
  if n + i >= String.length s then i else
  match s.[n+i] with
  | '0' .. '9' -> count_digits s n (i + 1)
  | _ -> i
;;

let rec count_nondigits s n i =
  if n + i >= String.length s then i else
  match s.[n+i] with
  | '0' .. '9' -> i
  | _ -> count_nondigits s n (i + 1)
;;

let rec lex s n =
  if n >= String.length s then [] else
  match s.[n] with
  | '0' .. '9' ->
     let l = count_digits s n 0 in
     Int (String.sub s n l) :: lex s (n + l)
  | _ ->
     let l = count_nondigits s n 0 in
     String (String.sub s n l) :: lex s (n + l)
;;

type token =
  | S of string
  | I of int * int   (* base, incr *)
;;

exception Mismatch;;
exception Bad_template of string;;
exception Bad_number of int;;

let split_string s =
  let l = String.length s in
  let m = l mod 2 in
  let rec loop i =
    if i = l / 2 then ([], s)
    else begin
      let s1 = String.sub s 0 (l / 2 - i) in
      let s2 = String.sub s (l / 2 + i + m) (l / 2 - i) in
      if s1 = s2 then begin
        let sep = String.sub s (l / 2 - i) (2 * i + m) in
        ([S s1], sep)
      end else loop (i + 1)
    end
  in
  loop 0
;;

let split_int s =
  let l = String.length s in
  if l mod 2 = 1 then raise Mismatch;
  let n1 = int_of_string (String.sub s 0 (l / 2)) in
  let n2 = int_of_string (String.sub s (l / 2) (l / 2)) in
  ([I (n1, n2 - n1)], "")
;;

let rec prefix n l =
  if n = 0 then [] else
  match l with
  | [] -> assert false
  | h :: t -> h :: (prefix (n-1) t)
;;

let rec suffix n l =
  if n = 0 then l else
  match l with
  | [] -> assert false
  | h :: t -> suffix (n-1) t
;;

let rec correlate l1 l2 =
  let f x y =
    match x, y with
    | String s1, String s2 when s1 = s2 -> S s1
    | Int s1, Int s2 ->
       let n1 = int_of_string s1 in
       let n2 = int_of_string s2 in
       I (n1, n2 - n1)
    | _, _ -> raise Mismatch
  in
  try List.map2 f l1 l2
  with Invalid_argument _ -> assert false
;;

let rec is_prefix pre s n =
  if n >= String.length pre then true
  else if n >= String.length s then false
  else pre.[n] = s.[n] && is_prefix pre s (n+1)
;;

let rec is_suffix suf s n =
  let lsuf = String.length suf in
  let ls = String.length s in
  if n > lsuf then true
  else if n > ls then false
  else suf.[lsuf - n] = s.[ls - n] && is_suffix suf s (n+1)
;;

let rec last l =
  match l with
  | [] -> assert false
  | [x] -> x
  | _ :: t -> last t
;;

let split_sep pre mid suf =
  let pre1, lpre =
    match pre with
    | String s when is_prefix s mid 0 -> ([pre], String.length s)
    | Int _ -> ([], 0)
    | _ -> raise Mismatch
  in
  let suf1, lsuf =
    match suf with
    | String s when is_suffix s mid 1 -> ([suf], String.length s)
    | Int _ -> ([], 0)
    | _ -> raise Mismatch
  in
  if lpre + lsuf > String.length mid then raise Mismatch;
  (pre1, String.sub mid lpre (String.length mid - lpre - lsuf), suf1)
;;

let split_sep2 pre mid1 mid2 suf =
  match pre, mid1, mid2, suf with
  | String spre, String smid1, Int _, Int _ when is_prefix spre smid1 0 ->
     let lmid1 = String.length smid1 in
     let lpre = String.length spre in
     ([pre], String.sub smid1 lpre (lmid1 - lpre), [mid2])
  | Int _, Int _, String smid2, String ssuf when is_suffix ssuf smid2 1 ->
     let lmid2 = String.length smid2 in
     let lsuf = String.length ssuf in
     ([mid1], String.sub smid2 0 (lmid2 - lsuf), [suf])
  | _ -> assert false
;;

let parse s =
  try
    let l = lex s 0 in
    let len = List.length l in
    match l with
    | [] -> ([], "")
    | [String x] -> split_string x
    | [Int x] -> split_int x
    | _ when len mod 4 = 0 ->
       let pre = prefix (len / 2 - 1) l in
       let suf = suffix (len / 2 + 1) l in
       let mid1 = List.nth l (len / 2 - 1) in
       let mid2 = List.nth l (len / 2) in
       let (pre1, sep, suf1) = split_sep2 (last suf) mid1 mid2 (List.hd pre) in
       (correlate (pre @ pre1) (suf1 @ suf), sep)
    | _ when len mod 2 = 1 ->
       let pre = prefix (len / 2) l in
       let suf = suffix (len / 2 + 1) l in
       let mid =
         match List.nth l (len / 2) with
         | Int _ -> raise Mismatch
         | String s -> s
       in
       let (pre1, sep, suf1) = split_sep (last suf) mid (List.hd pre) in
       (correlate (pre @ pre1) (suf1 @ suf), sep)
    | _ -> raise Mismatch
  with Mismatch -> raise (Bad_template s)
;;

let expand_string n s =
  if n < 0 then raise (Bad_number n);
  let (pattern, sep) = parse s in
  let rec instance l i accu =
    match l with
    | [] -> accu
    | S s :: t -> instance t i (s :: accu)
    | I (base, incr) :: t ->
       instance t i (string_of_int (base + i * incr) :: accu)
  in
  let rec loop i accu =
    if i >= n
    then accu
    else loop (i+1) (instance pattern i (sep :: accu))
  in
  if n = 0
  then ""
  else String.concat "" (List.rev (loop 1 (instance pattern 0 [])))
;;

let expand_string_rev n s =
  if n < 0 then raise (Bad_number n);
  let (pattern, sep) = parse s in
  let rec instance l i accu =
    match l with
    | [] -> accu
    | S s :: t -> instance t i (s :: accu)
    | I (base, incr) :: t ->
       instance t i (string_of_int (base + incr - i * incr) :: accu)
  in
  let rec loop i accu =
    if i < 0
    then accu
    else loop (i-1) (instance pattern i (sep :: accu))
  in
  if n = 0
  then ""
  else String.concat "" (List.rev (loop (n - 2) (instance pattern (n - 1) [])))
;;


let check2 c s i =
  i + 1 < String.length s && s.[i] = c && s.[i+1] = c
;;

let trim_nl s =
  let l = String.length s in
  if l >= 2 && s.[0] = '\n' && s.[l-1] = '\n'
  then String.sub s 1 (l - 2)
  else if l >= 4 && s.[0] = '\r' && s.[1] = '\n'
          && s.[l-2] = '\r' && s.[l-1] = '\n'
  then String.sub s 2 (l - 4)
  else raise (Bad_template s)
;;

let rec read_num s i0 scale i accu =
  if i < String.length s then begin
    match s.[i] with
    | '0' .. '9' ->
       let newaccu = (10 * accu + Char.code (s.[i]) - Char.code ('0')) in
       read_num s i0 scale (i+1) newaccu
    | ']' -> (scale * accu, i+1)
    | _ -> (0, i0)
  end else
    (0, i0)
;;

let read_suffix s i =
  if i + 2 < String.length s && s.[i] = '[' && s.[i+1] = 'n' then begin
    match s.[i+2] with
    | ']' -> (0, i+3)
    | '-' -> read_num s i (-1) (i+3) 0
    | '+' -> read_num s i 1 (i+3) 0
    | _ -> (0, i)
  end else
    (0, i)
;;

let expand_text n s =
  let rec copy i0 i accu =
    let cur () = String.sub s i0 (i - i0) in
    if i >= String.length s
    then cur () :: accu
    else if s.[i] = '@' && check2 '@' s (i+1)
    then expand (i + 3) (i + 3) (cur () :: accu)
    else if s.[i] = '.' && check2 '.' s (i+1)
    then expand_rev (i + 3) (i + 3) (cur () :: accu)
    else copy i0 (i + 1) accu
  and expand i0 i accu =
    let cur () = String.sub s i0 (i - i0) in
    if i >= String.length s
    then raise (Bad_template s)
    else if s.[i] = '.' && check2 '.' s (i+1)
    then begin
      let pat = cur () in
      let (p, iend) = read_suffix s (i+3) in
      let exp = try expand_string (n + p) pat
        with Bad_template _ -> expand_string (n + p) (trim_nl pat)
      in
      copy iend iend (exp :: accu)
    end else expand i0 (i + 1) accu
  and expand_rev i0 i accu =
    let cur () = String.sub s i0 (i - i0) in
    if i >= String.length s
    then raise (Bad_template s)
    else if s.[i] = '@' && check2 '@' s (i+1)
    then begin
      let pat = cur () in
      let (p, iend) = read_suffix s (i+3) in
      let exp = try expand_string_rev (n + p) pat
        with Bad_template _ -> expand_string_rev (n + p) (trim_nl pat)
      in
      copy iend iend (exp :: accu)
    end else expand_rev i0 (i + 1) accu
  in
  String.concat "" (List.rev (copy 0 0 []))
;;
