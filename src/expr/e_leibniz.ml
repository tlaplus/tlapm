(*
 * expr/leibniz.ml --- detect leibniz positions
 *
 * This info is added as an array to the property of all Operators and
 * applications of operators to arguments.
 *
 * Copyright (C) 2008-2014  INRIA and Microsoft Corporation
 *)

open Ext
open Property

open E_t


module Visit = E_visit

let isleibniz : bool array pfuncs =
  Property.make "Expr.Leibniz.isleibniz"

let is_leibniz x n = Array.get (Property.get x isleibniz) n
let has_leibniz x = Property.has x isleibniz

let compute_array scx e =
  (*
   * the Leibnizier sets the reference to true iff the ith index is not in the
   * scope of a non-leibniz operator.
   * There are three arguments:
     * a bool denoting if the scope is leibniz
     * an int denoting the de bruijn index of the searched for variable
     * a reference denoting the return value
   * This means we do the following in the visitor:
     * - (*A*) visit the db index denoted by index and set the reference to false if
       * the scope is false
       - (*B*) update the index everytime we encounter an abstraction
       - (*C*) set the scope to false when visiting into a non-leibniz argument
   *)
  let leibnizier = object (self : 'self)
    inherit [(bool * int * bool ref)] Visit.iter as super

    method expr scx e =
      let ((scp,ind,rf),cx) = scx in match e.core with
      | Ix n when ind = n && scp = false -> rf := false (*A*)
      | Lambda (vs, e) -> (*B*)
          let scx = E_visit.adjs scx (List.map (fun (v, shp) -> Fresh (v, shp, Unknown, Unbounded) @@ v) vs) in
          self#expr ((scp,ind+(List.length vs),rf),snd scx) e
      (*C*)
      | Apply ({core = Internal (Builtin.Prime | Builtin.Box _ | Builtin.Diamond)}, [e]) ->
          self#expr ((false,ind,rf),snd scx) e
      | Apply ({core = Internal (Builtin.Leadsto | Builtin.Actplus)}, [e1;e2]) ->
          self#expr ((false,ind,rf),snd scx) e1; self#expr ((false,ind,rf),snd
          scx) e2
      | Apply ({core = Ix n}, args) -> begin
          if n > Deque.size (snd scx) then
            Errors.bug ~at:e "Expr.Leibniz: unknown bound variable"
          else match Deque.nth ~backwards:true (snd scx) (n - 1) with
              | Some {core = Defn ({core = Operator(_,_)} as op, _, _, _)} ->
                List.iteri (fun i arg ->
                  self#expr ((is_leibniz op i,ind,rf),snd scx) arg
                ) args
              | _ -> super#expr scx e
        end
      | _ -> super#expr scx e
  end

  in match e.core with
    | Lambda (vars, e) -> Array.init (List.length vars) (fun i ->
        let r = ref true in
        let scx = E_visit.adjs scx (List.map (fun (v, shp) -> Fresh (v, shp, Unknown,
        Unbounded) @@ v) vars) in
        let () = leibnizier#expr ((true,i+1,r),(snd scx)) e in !r)
    | _ -> Array.make 0 true

class virtual leibniz_visitor = object (self : 'self)
  inherit [unit] Visit.map as super

  method expr scx ex = if (has_leibniz ex) then ex
          else match ex.core with
    (*
     * Temporary fix: in the presence of so arguments, mark all positions as
     * non-leibniz as a crude approximation..
     *
     * In the future:
     * in addition to assiging this information to Operators,
     * we need to assign leibnizity to applications of operators to
     * arguments as follows: the ith argument of the application is leibniz if:
       * the ith argument of the operator is leibniz and either:
         * 1) the argument is a first-order operator all of whose argument
         * positions are leibniz
         * 2) the argument is a term and in the definition of the operator, the
         * variable associated with this term does not occur as a subterm of a
         * variable associated with a non-lebniz argument. This means we need to
         * evaluate all second-order arguments first
    *)
    | Apply ({core = Ix n} as ixa, args) -> begin
        if n > Deque.size (snd scx) then
          Errors.bug ~at:ex "Expr.Leibniz: unknown bound variable"
        else match Deque.nth ~backwards:true (snd scx) (n - 1) with
            | Some {core = Defn ({core = Operator(_,e)}, _, _, _)} ->
            begin
              let assign_to_expr e ar = assign e isleibniz ar in
              (*
               * Right now we just check if the operator, i.e. the lambda
               * expression e, has sol arguments by checking the shapes of the
               * lambda expression. Later we imporve the approximation as
               * written in the paper about Coalescing
               * *)
              match e.core with
              | Lambda (vs,_) ->
                  let args = List.map (
                    fun e -> self#expr scx e
                  ) args in
                  (*
                   * right now we have a fixed value to assign
                   * to all arguments of the application  based if one
                   * bound variable is sol
                   * *)
                  let vl =  not (List.exists (
                    fun (_,shp) -> match shp with
                    | Shape_op _ -> true
                    | _ -> false
                  ) vs) in
                  assign_to_expr (Apply (ixa, args) @@ ex) (Array.make
                  (List.length args) vl)
              | _ ->
                  let ex = super#expr scx ex in
                  assign_to_expr ex (Array.make (List.length args) true)
            end
            | _ -> super#expr scx ex
      end
    | _ -> super#expr scx ex

  method hyp scx h = if (has_leibniz h) then (scx,h) else match h.core with
    (*
     * we assign leibnizity to operator arguments using an array
     * *)
    | Defn ({core=Operator (nm, e)} as op, wd, vis, ex) ->
      let e = self#expr scx e in
      let ar = compute_array scx e in
      let op = assign (Operator (nm, e) @@ op) isleibniz ar in
      let h = Defn (op, wd, vis, ex) @@ h in
      (E_visit.adj scx h, h)
    | _ -> super#hyp scx h

  method pform scx p = if (has_leibniz p) then p else super#pform scx p
  method defn scx p = if (has_leibniz p) then p else super#defn scx p
end
