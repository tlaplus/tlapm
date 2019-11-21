(*
 * lazyList.ml --- lazy lists
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

Revision.f "$Rev$";;

open Lazy

type 'a llist = Ll of 'a front Lazy.t

and 'a front =
  | Nil
  | Cons of 'a * 'a llist

type 'a t = 'a llist

let expose (Ll ll) = Lazy.force ll
let exact fr = Ll (lazy_from_val fr)
let delay fr = Ll (lazy_from_fun fr)

let empty = exact Nil
let cons x ll = exact (Cons (x, ll))

let null ll = match expose ll with
  | Nil -> true
  | _ -> false

let rec map f ll = delay begin fun () ->
  match expose ll with
    | Nil -> Nil
    | Cons (a, ll) ->
        Cons (f a, map f ll)
end

let rec filter f ll = delay begin fun () ->
  match expose ll with
    | Nil -> Nil
    | Cons (a, ll) ->
        let ll = filter f ll in
          if f a then Cons (a, ll) else expose ll
end

let rec filter_map f ll = delay begin fun () ->
  match expose ll with
    | Nil -> Nil
    | Cons (a, ll) ->
        let ll = filter_map f ll in
          match f a with
            | None -> expose ll
            | Some b -> Cons (b, ll)
end

let rev ll =
  let rec doit ll acc = match expose ll with
    | Nil -> acc
    | Cons (a, ll) ->
        doit ll (Cons (a, exact acc))
  in
    delay begin fun () ->
      doit ll Nil
    end

let rec fold_left f a ll =
  match expose ll with
    | Nil -> a
    | Cons (b, ll) ->
        fold_left f (f a b) ll

(** lifted straight from ExtList *)
let fold_right_max = 100
let fold_right f ll init =
  let rec tail_loop acc ll = match expose ll with
      | Nil -> acc
      | Cons (h, t) ->
          tail_loop (f h acc) t
  in
  let rec loop n ll = match expose ll with
    | Nil -> init
    | Cons (h, t) ->
        if n < fold_right_max then
          f h (loop (n+1) t)
        else
          f h (tail_loop init (rev t))
  in
    loop 0 ll

let rec unfold i f = delay begin fun () ->
  match f i with
    | Some (x, i) ->
        Cons (x, unfold i f)
    | None ->
        Nil
end

let length ll = fold_left (fun n _ -> n + 1) 0 ll

let rec split inits ll = function
  | 0 -> (inits, ll)
  | n -> (match expose ll with
            | Nil -> failwith "LazyList.split"
            | Cons (a, ll) ->
                split (a :: inits) ll (n - 1))


let hd ll =
  match expose ll with
    | Nil -> failwith "LazyList.hd"
    | Cons (a, ll) -> a

let tl ll = delay
  (fun () ->
     match expose ll with
       | Cons (a, ll) -> expose ll
       | Nil -> failwith "LazyList.tl")

let rec take n ll =
  if n = 0 then empty
  else (match expose ll with
          | Nil -> failwith "LazyList.take"
          | Cons (a, ll) ->
              cons a (take (n - 1) ll))

let drop n ll = delay (fun () -> expose (snd (split [] ll n)))

let rec (@@) ll mm = delay begin fun () ->
  match expose ll with
    | Nil ->
        expose mm
    | Cons (a, ll) ->
        Cons (a, ll @@ mm)
end

let rec concat = function
  | [] -> empty
  | ll :: lls ->
      ll @@ concat lls

let rec make gen = delay begin
  fun () ->
    match gen () with
      | None -> Nil
      | Some a -> Cons (a, make gen)
end

(*
 * let expose (Ll ll) = match force ll with
 *   | Nil -> None
 *   | Cons (a, l) -> Some (a, l)
 *)

let exact (a, ll) = exact (Cons (a, ll))

let delay lf = delay (fun () -> let (a, ll) = lf () in Cons (a, ll))
