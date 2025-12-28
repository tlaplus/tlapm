module TL = Tlapm_lib

let of_goal (ex : TL.Expr.T.expr) : TL.Expr.T.sequent =
  { context = TL.Util.Deque.empty; active = ex }
