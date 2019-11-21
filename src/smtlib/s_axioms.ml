(*
 * smtlib/axioms.ml -- axioms for untyped encoding
 *
 *
 * Copyright (C) 2008-2010  INRIA and Microsoft Corporation
 *)

open Ext

open S_t
open S_symbs


let bool_smb  = core_smb CoreBool
let true_smb  = core_smb CoreTrue
let false_smb = core_smb CoreFalse
let not_smb   = core_smb CoreNot
let imp_smb   = core_smb CoreImp
let and_smb   = core_smb CoreAnd
let or_smb    = core_smb CoreOr
let eq_smb    = core_smb CoreEq
let neq_smb   = core_smb CoreNeq
let ite_smb   = core_smb CoreIte

let int_smb   = ints_smb IntsInt
let plus_smb  = ints_smb IntsPlus
let minus_smb = ints_smb IntsSubs
let mult_smb  = ints_smb IntsMult
let div_smb   = ints_smb IntsDiv
let mod_smb   = ints_smb IntsMod
let le_smb    = ints_smb IntsLe

let u_smb           = sets_smb U
let in_smb          = sets_smb In
let subset_smb      = sets_smb Subset
let enum_set_smb n  = sets_smb (SetEnum n)
let power_set_smb   = sets_smb PowerSet
let union_set_smb   = sets_smb UnionSet
let inter_smb       = sets_smb Inter
let union_smb       = sets_smb Union
let diff_smb        = sets_smb Diff

let bool_set_smb    = bools_smb BSet
let bool_cast_smb   = bools_smb BCast

let string_sort_smb = strings_smb SSort
let string_set_smb  = strings_smb SSet
let string_cast_smb = strings_smb SCast

let int_set_smb     = uints_smb ISet
let nat_set_smb     = uints_smb NSet
let int_cast_smb    = uints_smb ICast
let int_plus_smb    = uints_smb IPlus
let int_minus_smb   = uints_smb IMinus
let int_mult_smb    = uints_smb IMult
let int_div_smb     = uints_smb IDiv
let int_mod_smb     = uints_smb IMod
let int_le_smb      = uints_smb ILe
let range_smb       = uints_smb IRange

let fun_set_smb     = funs_smb FunSet
let dom_set_smb     = funs_smb DomSet
let fun_app_smb     = funs_smb FunApp
let fun_except_smb  = funs_smb FunExcept

let prod_set_smb n  = tuples_smb (ProdSet n)
let tuple_smb n     = tuples_smb (Tuple n)

let rec_set_smb n   = recs_smb (RecSet n)
let record_smb n    = recs_smb (Record n)


let mk_vbind smb = (smb, sort u_smb)


let no_intersect (s1, c1) (s2, c2) =
  forall ["x", sort s1; "a", sort s2] (
    bin neq_smb (una c1 (cst "x")) (una c2 (cst "a"))
  )

(* Sets *)

let set_ext =
  forall ["x", sort u_smb; "y", sort u_smb] (
    bin imp_smb (
      forall ["z", sort u_smb] (
        bin eq_smb (
          bin in_smb (cst "z") (cst "x")
        ) (
          bin in_smb (cst "z") (cst "y")
        )
      )
    ) (
      bin eq_smb (cst "x") (cst "y")
    )
  )

let subset_def =
  forall ["x", sort u_smb; "y", sort u_smb] (
    Annot (
      bin eq_smb (
        bin subset_smb (cst "x") (cst "y")
      ) (
        forall ["z", sort u_smb] (
          bin imp_smb (
            bin in_smb (cst "z") (cst "x")
          ) (
            bin in_smb (cst "z") (cst "y")
          )
        )
      ),
      ["pattern", Some (AttrList [
        bin subset_smb (cst "x") (cst "y")
      ])]
    )
  )

let enum_set_car n =
  let pars = List.init n (fun i -> "x" ^ string_of_int i) in
  forall (List.append (List.map mk_vbind pars) ["x", sort u_smb]) (
    Annot (
      bin eq_smb (
        bin in_smb (cst "x") (
          app (enum_set_smb n) (List.map cst pars)
        )
      ) (
        if n = 0 then
          cst false_smb
        else
          app or_smb (List.map begin fun smb ->
            bin eq_smb (cst "x") (cst smb)
          end pars)
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "x") (app (enum_set_smb n) (List.map cst pars))
      ])]
    )
  )

let power_set_car =
  forall ["x", sort u_smb; "z", sort u_smb] (
    Annot (
      bin eq_smb (
        bin in_smb (cst "z") (una power_set_smb (cst "x"))
      ) (
        forall ["y", sort u_smb] (
          bin imp_smb (
            bin in_smb (cst "y") (cst "z")
          ) (
            bin in_smb (cst "y") (cst "x")
          )
        )
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "z") (una power_set_smb (cst "x"))
      ])]
    )
  )

let union_set_car =
  forall ["x", sort u_smb; "z", sort u_smb] (
    Annot (
      bin eq_smb (
        bin in_smb (cst "z") (una union_set_smb (cst "x"))
      ) (
        exists ["y", sort u_smb] (
          bin and_smb (
            bin in_smb (cst "y") (cst "x")
          ) (
            bin in_smb (cst "z") (cst "y")
          )
        )
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "z") (una union_set_smb (cst "x"))
      ])]
    )
  )

let inter_car =
  forall ["x", sort u_smb; "y", sort u_smb; "z", sort u_smb] (
    Annot (
      bin eq_smb (
        bin in_smb (cst "z") (bin inter_smb (cst "x") (cst "y"))
      ) (
        bin and_smb (
          bin in_smb (cst "z") (cst "x")
        ) (
          bin in_smb (cst "z") (cst "y")
        )
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "z") (bin inter_smb (cst "x") (cst "y"))
      ])]
    )
  )

let union_car =
  forall ["x", sort u_smb; "y", sort u_smb; "z", sort u_smb] (
    Annot (
      bin eq_smb (
        bin in_smb (cst "z") (bin union_smb (cst "x") (cst "y"))
      ) (
        bin or_smb (
          bin in_smb (cst "z") (cst "x")
        ) (
          bin in_smb (cst "z") (cst "y")
        )
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "z") (bin union_smb (cst "x") (cst "y"))
      ])]
    )
  )

let diff_car =
  forall ["x", sort u_smb; "y", sort u_smb; "z", sort u_smb] (
    Annot (
      bin eq_smb (
        bin in_smb (cst "z") (bin diff_smb (cst "x") (cst "y"))
      ) (
        bin or_smb (
          bin in_smb (cst "z") (cst "x")
        ) (
          bin in_smb (cst "z") (cst "y")
        )
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "z") (bin diff_smb (cst "x") (cst "y"))
      ])]
    )
  )

(* (Specialized) extensionality axioms *)

let empty_ext =
  forall ["a", sort u_smb] (
    Annot (
      bin imp_smb (
        bin neq_smb (cst "a") (cst (enum_set_smb 0))
      ) (
        exists ["x", sort u_smb] (
          bin in_smb (cst "x") (cst "a")
        )
      ),
      ["pattern", Some (AttrList [
        bin eq_smb (cst "a") (cst (enum_set_smb 0))
      ])
      ;"pattern", Some (AttrList [
        bin neq_smb (cst "a") (cst (enum_set_smb 0))
      ])]
    )
  )

(* Bools *)

let bool_set_car =
  forall ["b", sort u_smb] (
    Annot (
      bin eq_smb (
        bin in_smb (cst "b") (cst bool_set_smb)
      ) (
        bin or_smb (
          bin eq_smb (cst "b") (una bool_cast_smb (cst true_smb))
        ) (
          bin eq_smb (cst "b") (una bool_cast_smb (cst false_smb))
        )
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "b") (cst bool_set_smb)
      ])]
    )
  )

let bool_cast_inj =
  bin neq_smb (
    una bool_cast_smb (cst true_smb)
  ) (
    una bool_cast_smb (cst false_smb)
  )

(* Strings *)

let string_set_car =
  forall ["s", sort u_smb] (
    Annot (
      bin eq_smb (
        bin in_smb (cst "s") (cst string_set_smb)
      ) (
        exists ["str", sort string_sort_smb] (
          bin eq_smb (cst "s") (una string_cast_smb (cst "str"))
        )
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "s") (cst string_set_smb)
      ])]
    )
  )

let string_distinct s1 s2 =
  bin neq_smb (cst s1) (cst s2)

let string_cast_inj =
  forall ["s", sort string_sort_smb; "t", sort string_sort_smb] (
    Annot (
      bin imp_smb (
        bin eq_smb (
          una string_cast_smb (cst "s")
        ) (
          una string_cast_smb (cst "t")
        )
      ) (
        bin eq_smb (cst "s") (cst "t")
      ),
      ["pattern", Some (AttrList [
        bin eq_smb (
          una string_cast_smb (cst "s")
        ) (
          una string_cast_smb (cst "t")
        )
      ])]
    )
  )

(* Ints *)

let int_set_car =
  forall ["x", sort u_smb] (
    Annot (
      bin eq_smb (
        bin in_smb (cst "x") (cst int_set_smb)
      ) (
        exists ["n", sort int_smb] (
          bin eq_smb (
            cst "x"
          ) (una int_cast_smb (cst "n"))
        )
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "x") (cst int_set_smb)
      ])]
    )
  )

let nat_set_car =
  forall ["x", sort u_smb] (
    Annot (
      bin eq_smb (
        bin in_smb (cst "x") (cst nat_set_smb)
      ) (
        bin and_smb (
          bin in_smb (cst "x") (cst int_set_smb)
        ) (
          bin int_le_smb (una int_cast_smb (intlit 0)) (cst "x")
        )
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "x") (cst nat_set_smb)
      ])]
    )
  )

let int_cast_inj =
  forall ["m", sort int_smb; "n", sort int_smb] (
    Annot (
      bin imp_smb (
        bin eq_smb (
          una int_cast_smb (cst "m")
        ) (
          una int_cast_smb (cst "n")
        )
      ) (
        bin eq_smb (cst "m") (cst "n")
      ),
      ["pattern", Some (AttrList [
        bin eq_smb (
          una int_cast_smb (cst "m")
        ) (
          una int_cast_smb (cst "n")
        )
      ])]
    )
  )

let int_plus_hom =
  forall ["m", sort int_smb; "n", sort int_smb] (
    Annot (
      bin eq_smb (
        bin int_plus_smb (
          una int_cast_smb (cst "m")
        ) (
          una int_cast_smb (cst "n")
        )
      ) (
        una int_cast_smb (
          bin plus_smb (cst "m") (cst "n")
        )
      ),
      ["pattern", Some (AttrList [
        bin int_plus_smb (
          una int_cast_smb (cst "m")
        ) (
          una int_cast_smb (cst "n")
        )
      ])]
    )
  )

let int_minus_hom =
  forall ["m", sort int_smb; "n", sort int_smb] (
    Annot (
      bin eq_smb (
        bin int_minus_smb (
          una int_cast_smb (cst "m")
        ) (
          una int_cast_smb (cst "n")
        )
      ) (
        una int_cast_smb (
          bin minus_smb (cst "m") (cst "n")
        )
      ),
      ["pattern", Some (AttrList [
        bin int_minus_smb (
          una int_cast_smb (cst "m")
        ) (
          una int_cast_smb (cst "n")
        )
      ])]
    )
  )

let int_mult_hom =
  forall ["m", sort int_smb; "n", sort int_smb] (
    Annot (
      bin eq_smb (
        bin int_mult_smb (
          una int_cast_smb (cst "m")
        ) (
          una int_cast_smb (cst "n")
        )
      ) (
        una int_cast_smb (
          bin mult_smb (cst "m") (cst "n")
        )
      ),
      ["pattern", Some (AttrList [
        bin int_mult_smb (
          una int_cast_smb (cst "m")
        ) (
          una int_cast_smb (cst "n")
        )
      ])]
    )
  )

let int_div_hom =
  forall ["m", sort int_smb; "n", sort int_smb] (
    Annot (
      bin imp_smb (
        bin neq_smb (cst "n") (intlit 0)
      ) (
        bin eq_smb (
          bin int_div_smb (
            una int_cast_smb (cst "m")
          ) (
            una int_cast_smb (cst "n")
          )
        ) (
          una int_cast_smb (
            bin div_smb (cst "m") (cst "n")
          )
        )
      ),
      ["pattern", Some (AttrList [
        bin int_div_smb (
          una int_cast_smb (cst "m")
        ) (
          una int_cast_smb (cst "n")
        )
      ])]
    )
  )

let int_mod_hom =
  forall ["m", sort int_smb; "n", sort int_smb] (
    Annot (
      bin imp_smb (
        bin neq_smb (cst "n") (intlit 0)
      ) (
        bin eq_smb (
          bin int_mod_smb (
            una int_cast_smb (cst "m")
          ) (
            una int_cast_smb (cst "n")
          )
        ) (
          una int_cast_smb (
            bin mod_smb (cst "m") (cst "n")
          )
        )
      ),
      ["pattern", Some (AttrList [
        bin int_mod_smb (
          una int_cast_smb (cst "m")
        ) (
          una int_cast_smb (cst "n")
        )
      ])]
    )
  )

let int_le_hom =
  forall ["m", sort int_smb; "n", sort int_smb] (
    Annot (
      bin eq_smb (
        bin int_le_smb (
          una int_cast_smb (cst "m")
        ) (
          una int_cast_smb (cst "n")
        )
      ) (
        bin le_smb (cst "m") (cst "n")
      ),
      ["pattern", Some (AttrList [
        bin int_le_smb (
          una int_cast_smb (cst "m")
        ) (
          una int_cast_smb (cst "n")
        )
      ])]
    )
  )

let range_car =
  forall ["x", sort u_smb; "y", sort u_smb; "z", sort u_smb] (
    Annot (
      bin eq_smb (
        bin in_smb (cst "z") (bin range_smb (cst "x") (cst "y"))
      ) (
        bin and_smb (
          bin int_le_smb (cst "x") (cst "z")
        ) (
          bin int_le_smb (cst "z") (cst "y")
        )
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "z") (bin range_smb (cst "x") (cst "y"))
      ])]
    )
  )


(* Functions *)

let fun_ext =
  forall ["a", sort u_smb; "b", sort u_smb; "f", sort u_smb; "g", sort u_smb] (
    Annot (
      bin imp_smb (
        app and_smb [
          bin in_smb (cst "f") (bin fun_set_smb (cst "a") (cst "b"));
          bin in_smb (cst "g") (bin fun_set_smb (cst "a") (cst "b"));
          forall ["x", sort u_smb] (
            bin imp_smb (
              bin in_smb (cst "x") (cst "a")
            ) (
              bin eq_smb (
                bin fun_app_smb (cst "f") (cst "x")
              ) (
                bin fun_app_smb (cst "g") (cst "x")
              )
            )
          )
        ]
      ) (
        bin eq_smb (cst "f") (cst "g")
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "f") (bin fun_set_smb (cst "a") (cst "b"));
        bin in_smb (cst "g") (bin fun_set_smb (cst "a") (cst "b"))
      ])]
    )
  )

let fun_set_car =
  forall ["a", sort u_smb; "b", sort u_smb; "f", sort u_smb] (
    Annot (
      bin eq_smb (
        bin in_smb (cst "f") (bin fun_set_smb (cst "a") (cst "b"))
      ) (
        bin and_smb (
          bin eq_smb (una dom_set_smb (cst "f")) (cst "a")
        ) (
          forall ["x", sort u_smb] (
            bin imp_smb (
              bin in_smb (cst "x") (cst "a")
            ) (
              bin in_smb (bin fun_app_smb (cst "f") (cst "x")) (cst "b")
            )
          )
        )
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "f") (bin fun_set_smb (cst "a") (cst "b"))
      ])]
    )
  )

let fun_except_dom =
  forall ["f", sort u_smb; "d", sort u_smb; "v", sort u_smb] (
    Annot (
      bin eq_smb (
        una dom_set_smb (ter fun_except_smb (cst "f") (cst "d") (cst "v"))
      ) (
        una dom_set_smb (cst "f")
      ),
      ["pattern", Some (AttrList [
        una dom_set_smb (ter fun_except_smb (cst "f") (cst "d") (cst "v"))
      ])]
    )
  )

let fun_except_val =
  forall ["f", sort u_smb; "d", sort u_smb; "v", sort u_smb; "x", sort u_smb] (
    Annot (
      bin imp_smb (
        bin in_smb (cst "x") (una dom_set_smb (cst "f"))
      ) (
        bin eq_smb (
          bin fun_app_smb (ter fun_except_smb (cst "f") (cst "d") (cst "v")) (cst "x")
        ) (
          ter ite_smb (bin eq_smb (cst "x") (cst "d")) (cst "v") (
            bin fun_app_smb (cst "f") (cst "x")
          )
        )
      ),
      ["pattern", Some (AttrList [
        bin fun_app_smb (ter fun_except_smb (cst "f") (cst "d") (cst "v")) (cst "x")
      ])]
    )
  )

(* Tuples *)

let prod_set_car n =
  let pars = List.init n (fun i -> "s" ^ string_of_int i) in
  let vars = List.init n (fun i -> "x" ^ string_of_int i) in
  forall (List.append (List.map mk_vbind pars) ["x", sort u_smb]) (
    Annot (
      bin eq_smb (
        bin in_smb (cst "x") (app (prod_set_smb n) (List.map cst pars))
      ) (
        if n = 0 then
          bin eq_smb (cst "x") (cst (tuple_smb 0))
        else
          exists (List.map mk_vbind vars) (
            app and_smb (
              List.append (
                List.map2 (fun smb1 smb2 -> bin in_smb (cst smb1) (cst smb2)) vars pars
              ) (
                [bin eq_smb (cst "x") (app (tuple_smb n) (List.map cst vars))]
              )
            )
          )
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "x") (app (prod_set_smb n) (List.map cst pars))
      ])]
    )
  )

let tuple_ext n =
  let pars = List.init n (fun i -> "s" ^ string_of_int i) in
  forall (List.map mk_vbind (List.append pars ["t"])) (
    Annot (
      bin imp_smb (
        bin in_smb (cst "t") (app (prod_set_smb n) (List.map cst pars))
      ) (
        bin eq_smb (cst "t") (
          app (tuple_smb n) (
            List.init n (fun i ->
              bin fun_app_smb (cst "t") (una int_cast_smb (intlit (i+1)))
            )
          )
        )
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "t") (app (prod_set_smb n) (List.map cst pars))
      ])]
    )
  )

let tuple_def n i =
  let vars = List.init n (fun i -> "x" ^ string_of_int i) in
  forall (List.map mk_vbind vars) (
    Annot (
      bin eq_smb (
        bin fun_app_smb (
          app (tuple_smb n) (List.map cst vars)
        ) (
          una int_cast_smb (intlit i)
        )
      ) (
        cst (List.nth vars (i-1))
      ),
      ["pattern", Some (AttrList [
        bin fun_app_smb (
          app (tuple_smb n) (List.map cst vars)
        ) (
          una int_cast_smb (intlit i)
        )
      ])]
    )
  )

let tuple_dom n =
  let vars = List.init n (fun i -> "x" ^ string_of_int i) in
  forall (List.map mk_vbind vars) (
    Annot (
      bin eq_smb (
        una dom_set_smb (
          app (tuple_smb n) (List.map cst vars)
        )
      ) (
        bin range_smb (
          una int_cast_smb (intlit 1)
        ) (
          una int_cast_smb (intlit n)
        )
      ),
      []
    )
  )

(* Records *)

let rec_set_car n =
  let fields = List.init n (fun i -> "f" ^ string_of_int i) in
  let vars = List.init n (fun i -> "x" ^ string_of_int i) in
  forall (List.append (List.map mk_vbind fields) (List.append (List.map mk_vbind vars) ["r", sort u_smb])) (
    Annot (
      bin eq_smb (
        bin in_smb (cst "r") (app (rec_set_smb n) (List.map cst (List.append fields vars)))
      ) (
        app and_smb (
          bin eq_smb (
            una dom_set_smb (cst "r")
          ) (
            app (enum_set_smb n) (List.map cst fields)
          )
          :: List.map2 begin fun fsmb vsmb ->
            bin in_smb (bin fun_app_smb (cst "r") (cst fsmb)) (cst vsmb)
          end fields vars
        )
      ),
      ["pattern", Some (AttrList [
        bin in_smb (cst "r") (app (rec_set_smb n) (List.map cst (List.append fields vars)))
      ])]
    )
  )

let record_def n =
  let fields = List.init n (fun i -> "f" ^ string_of_int i) in
  let vars = List.init n (fun i -> "x" ^ string_of_int i) in
  forall (List.append (List.map mk_vbind fields) (List.map mk_vbind vars)) (
    Annot (
      app and_smb (
        List.map2 begin fun fsmb vsmb ->
          bin eq_smb (
            bin fun_app_smb (
              app (record_smb n) (List.map cst (List.append fields vars))
            ) (
              cst fsmb
            )
          ) (
            cst vsmb
          )
        end fields vars
      ),
      []
    )
  )

let record_dom n =
  let fields = List.init n (fun i -> "f" ^ string_of_int i) in
  let vars = List.init n (fun i -> "x" ^ string_of_int i) in
  forall (List.append (List.map mk_vbind fields) (List.map mk_vbind vars)) (
    Annot (
      bin eq_smb (
        una dom_set_smb (
          app (record_smb n) (List.map cst (List.append fields vars))
        )
      ) (
        app (enum_set_smb n) (List.map cst fields)
      ),
      []
    )
  )

