(*  Copyright 2001 INRIA  *)

type 'a tree =
  | Node of 'a * 'a tree * 'a tree
  | Leaf
;;

type 'a t = {
  cmp : 'a -> 'a -> int;
  tree : 'a tree;
  curpath : int;
};;

let empty cmp = {
  cmp = cmp;
  tree = Leaf;
  curpath = 0;
};;

let rec insert_aux cmp t x path =
  match t with
  | Leaf -> Node (x, Leaf, Leaf)
  | Node (y, b1, b2) ->
     let (here, next) = if cmp x y < 0 then (x, y) else (y, x) in
     let newpath = path lsr 1 in
     if path land 1 = 0
     then Node (here, insert_aux cmp b1 next newpath, b2)
     else Node (here, b1, insert_aux cmp b2 next newpath)
;;

let insert hp x = {
  cmp = hp.cmp;
  tree = insert_aux hp.cmp hp.tree x hp.curpath;
  curpath = hp.curpath + 1;
};;

let rec remove_aux cmp t =
  match t with
  | Leaf -> None
  | Node (y, Leaf, b2) -> Some (y, b2)
  | Node (y, b1, Leaf) -> Some (y, b1)
  | Node (y, (Node (z1, _, _) as b1), (Node (z2, _, _) as b2)) ->
     let (nb1, nb2) = if cmp z1 z2 < 0 then (b1, b2) else (b2, b1) in
     match remove_aux cmp nb1 with
     | Some (nz1, nnb1) -> Some (y, Node (nz1, nnb1, nb2))
     | None -> assert false
;;

let remove hp =
  match remove_aux hp.cmp hp.tree with
  | None -> None
  | Some (x, newtree) -> Some (x, { hp with tree = newtree })
;;

let head hp =
  match hp.tree with
  | Leaf -> None
  | Node (y, _, _) -> Some y
;;

let rec length_aux t =
  match t with
  | Leaf -> 0
  | Node (_, b1, b2) -> 1 + length_aux b1 + length_aux b2
;;

let length hp = length_aux hp.tree;;

let is_empty hp =
  match hp.tree with
  | Leaf -> true
  | Node _ -> false
;;

let rec iter_aux f = function
  | Leaf -> ()
  | Node (x, b1, b2) -> f x; iter_aux f b1; iter_aux f b2;
;;

let iter f hp = iter_aux f hp.tree;;
