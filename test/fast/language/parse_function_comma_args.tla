------------------------- MODULE parse_function_comma_args ---------------------
EXTENDS TLAPS


(* only for parsing, backends cannot yet handle this function *)
p1 == [m, n \in {1}, r \in {2} |-> m]

(* only for parsing, backends cannot yet handle this function *)
p2 == [<<m, n>> \in {1} \X {2}, r \in {3} |-> m]

(* only for parsing, backends cannot yet handle this function *)
f == [1 EXCEPT ![1, 2] = 1]


k == [<<m, n>> \in {1} \X {2} |-> m]


(* Proving this theorem requires the detection of Cartesian products
and tuplification of function signatures, and tuplification of
comma-separated arguments in function application.
*)
THEOREM k[<<1, 2>>] = 1
BY DEF k


g == [<<ab, c>> \in {1} \X {4}, <<a, bc>> \in {2} \X {3} |-> ab]


(* backends do not not support this expression yet *)
THEOREM g[<<<<1, 4>>, <<2, 3>>>>] = 1
BY SMT DEF g


h == [<<abc1, abc2>> \in ({1} \X {4}) \X ({2} \X {3}) |-> abc1[1]]


THEOREM h[<<<<1, 4>>, <<2, 3>>>>] = 1
BY Zenon DEF h


---------------------------------------------------------------------------


q1 == [a \in {1}, b \in {2} |-> a]
q2 == [<<a, b>> \in {1} \X {2} |-> a]


THEOREM q1[<<1, 2>>] = 1
BY Zenon DEF q1


THEOREM q2[<<1, 2>>] = 1
BY Zenon DEF q2

================================================================================
