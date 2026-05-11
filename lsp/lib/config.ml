type t = { decomposition_disj_cases : bool }

let default = { decomposition_disj_cases = false }
let set_decomposition_disj_cases v (_ : t) = { decomposition_disj_cases = v }
