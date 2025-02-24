(*
 * deque.ml --- Persistent functional double-ended queues
 *
 *
 * Copyright (C) 2008-2019  INRIA and Microsoft Corporation
 *)

open Ext

type 'a dq = { front : 'a list ; flen : int ;
               rear : 'a list  ; rlen : int }

let empty = { front = [ ] ; flen = 0 ;
              rear  = [ ] ; rlen = 0 }

let size q =
  q.flen + q.rlen

let cons x q =
  { q with front = x :: q.front ; flen = q.flen + 1 }

let snoc q x =
  { q with rear = x :: q.rear ; rlen = q.rlen + 1 }

let front q =
  match q.front with
    | h :: front -> Some (h, { q with front = front ; flen = q.flen - 1 })
    | _ ->
        match q.rear with
          | [] -> None
          | _ ->
              let front = List.rev q.rear in
              Some (List.hd front, { front = List.tl front ;
                                     flen = q.rlen - 1 ;
                                     rear = [] ;
                                     rlen = 0 })

let rear q =
  match q.rear with
    | t :: rear -> Some ({ q with rear = rear ; rlen = q.rlen - 1 }, t)
    | _ ->
        match q.front with
          | [] -> None
          | _ ->
              let rear = List.rev q.front in
              Some ({ front = [] ; flen = 0 ;
                      rear = List.tl rear ; rlen = q.flen - 1 },
                    List.hd rear)

let rev q = { front = q.rear ; flen = q.rlen ;
              rear = q.front ; rlen = q.flen }

let of_list l = { front = l ; flen = List.length l ;
                  rear = [] ; rlen = 0 }

let null q = size q = 0

let append_rl q r =
  let rec spin rear = function
    | [] -> r.rear @ rear
    | x :: rfront ->
        spin (x :: rear) rfront
  in { q with
         rlen = q.rlen + size r ;
         rear = spin q.rear r.front }

let append_lr q r =
  let rec spin front = function
    | [] -> q.front @ front
    | x :: qrear ->
        spin (x :: front) qrear
  in { r with
         flen = r.flen + size q ;
         front = spin r.front q.rear }

let append q r =
  if size q > size r then
    append_rl q r
  else
    append_lr q r

let append_list q l =
  let n = List.length l in
  let rec spin rear = function
    | [] -> rear
    | x :: l -> spin (x :: rear) l
  in { q with
         rear = spin q.rear l ;
         rlen = q.rlen + n }

let prepend_list l q =
  let n = List.length l in
  { q with
      front = l @ q.front ;
      flen = q.flen + n }

let rec nth ?(backwards=false) q n =
  (* Return item `n` from `q`.

  Define `m == (size q) - 1`.

  Indexing starts from 0, thus `q` contains
  elements indexed with:

    0, 1, ..., m

  If `backwards=true`, then count from the end,
  so the indexing becomes:

    m, m - 1, ..., 0
  *)
  if backwards then nth (rev q) n
  else if n >= size q then None
  else
    let rec git q n =
      match front q with
        | Some (x, q) ->
            if n = 0 then Some x else git q (n - 1)
        | None ->
            failwith "Deque.nth: internal error"
    in
    git q n

let rec first_n q n =
    (* Return the first `n` elements of the queue `q`. *)
    if (n < 0) then
        failwith (Printf.sprintf "Deque.first_n:  n = %d < 0" n);
    if (n > (size q)) then
        failwith (Printf.sprintf "Deque.first_n:  n = %d > size q = %d" n (size q));
    let rec f q n =
        assert (n <= size q);
        assert (n >= 0);
        match n with
        | 0 -> empty
        | _ -> begin match front q with
            | None -> assert false
            | Some (x, q) ->
                let r = f q (n - 1) in
                cons x r
            end
    in
    (* TODO: move this unit test *)
    (* assert ((size (f empty 0)) == 0); *)
    f q n


let map f q =
  let rec go n q r = match front q with
    | None -> r
    | Some (x, q) ->
        go (n + 1) q (snoc r (f n x))
  in
  go 0 q empty

let iter f q =
  let rec go n q = match front q with
    | None -> ()
    | Some (x, q) ->
        f n x ;
        go (n + 1) q
  in
  go 0 q

let rec fold_left fn acc q = match front q with
  | None -> acc
  | Some (f, q) -> fold_left fn (fn acc f) q

let rec fold_right fn q acc = match rear q with
  | None -> acc
  | Some (q, r) -> fold_right fn q (fn r acc)

let to_list q =
  let rec go l q = match rear q with
    | None -> l
    | Some (q, x) ->
        go (x :: l) q
  in
  go [] q

let find ?(backwards=false) q test =
  let rec spin k f r = match f with
    | [] -> begin match r with
        | [] -> None
        | _ -> spin k (List.rev r) []
      end
    | x :: f ->
        if test x then Some (k, x)
        else spin (k + 1) f r
  in
  if backwards then
    spin 0 q.rear q.front
  else
    spin 0 q.front q.rear

let alter ?(backwards=false) q n alt_fn =
  let n = if backwards then size q - n - 1 else n in
  let newq = ref empty in
  let rec spin k q = match front q with
    | None -> invalid_arg "alter"
    | Some (x, q) ->
        if k = n then
          append !newq (cons (alt_fn x) q)
        else begin
          newq := snoc !newq x ;
          spin (k + 1) q
        end
  in
  spin 0 q

(* Compare deques `q1` and `q2`, using `cmp` to compare their elements. *)
let equal cmp q1 q2 =
  let rec diff l1 l2 =
    match l1, l2 with
    | x1 :: ll1, x2 :: ll2 when cmp x1 x2 -> diff ll1 ll2
    | [], _ -> Some l2
    | _, [] -> Some l1
    | _ -> None
  in
  q1.flen + q1.rlen = q2.flen + q2.rlen && begin
    let f = diff q1.front q2.front in
    let r = diff q1.rear q2.rear in
    match f, r with
    | Some lf, Some lr -> List.for_all2 cmp lf (List.rev lr)
    | _, _ -> false
  end
